/-
**The one-thread consumer at any call depth on the canonical AArch64
target** (`canonical 1`): `Correct` for a one-thread program whose source
thread calls code blocks, from an invariant of `OutS` rows
(`Spike/Lib/SegS.lean`) over fragments with the source thread's suspended
frames. The twin of `Spike/Lib/A64Consumer.lean` (whose statements are
unchanged), with the frames:

- `InvS`, `OwnS`: the fragment and the owned words get the frames
  (`State → Ctl → List Frame → Prop`, `State → List Frame → List (Loc × Val)`).
- `IRun`: the pairs a frame run reaches from the fragment (an `OutS.pre`
  row's control: the source has taken a pending return); `PendN`: a pair
  whose source has a pending frame run into the fragment (an `OutS.frame`
  row's landing, before the source's call or return), not at `main`'s
  return.
- `PlacedS`: every frame's environment placed (`frameEnvs`, `frameFv`,
  `frameTerms` order); `PlacedS.ofNil`.
- `msOfS`: `msOf` at the frames `fs` (the words owned at `fs`; a pair is
  placed for `main`'s exit only at depth 0).
- `NodesS`, `AbortPathS`, `TakePathS`, `SrcSafeS`: the obligations. `out`
  is an `OutS` row; `noRet` only at depth 0; `cell`, `noAlloc` and
  `SrcSafeS` over `IRun`; `ownRun`: a frame run at a state does not change
  the words owned there; `ownInstr`, `ownSys` at the frames of the row;
  `AbortPathS.at_`: the overflow site with every frame's environment small
  (`EnvSmallS`), or the heap site (`HeapReady`).
- `PreJ`, `PreS`, `PostS`, `RS`: the relation; the source thread's stack is
  the fragment's frames.
- `pre_stepS`, `pre_progressS`, `ti_stepS`, `r_abortS`, `components_oneS`,
  `correctKOnS`, `correctKS`: as in `A64Consumer`, every source run a frame
  run (`FrameRun.run_source_nil`); a row's frame run is taken with the row,
  its landing's pending run after it (`pend_land`). `PreJ` also keeps
  `HeapCtr` (the heap abort, with the budget's `cells` the arena's) and
  `FreshInv` (the next label unplaced); `pre_loadS` starts them (`hfr0`).
- `PreCoreJ`, `core_stepS`, `core_sysS`, `core_siteS`, `promSharedS`:
  `PromSharedS` discharged as in `Spike/Lib/A64PromShared.lean`, so
  `correctKOnS` has no `PromShared` hypothesis.
-/
import Spike.Lib.A64Consumer
import Spike.Lib.A64PromShared
import Spike.Lib.SegS
import Spike.Lib.HeapAbort
import Spike.Lib.FreshSrc
import Spike.Lib.SrcMemN

namespace Spike.Lib.A64ConsumerS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer

variable {P : SrcSem.SrcParams} {p : Prog} {E : Entry}

/-! ## Fragments with frames -/

/-- **The fragment with frames** of thread states paired with source
controls and the source thread's suspended frames, under a placement and
sizes of the labels. -/
abbrev InvS := Lbl → Lsize → FragS isaLSE2

/-- **The runtime words a thread state owns at the source frames `fs`**,
with their values. -/
abbrev OwnS := State → List TermRun.Frame → List (Loc × Val)

/-- **The pairs a frame run reaches from the fragment**, at the same state
(an `OutS.pre` row's control). -/
def IRun (p : Prog) (I : InvS) : InvS := fun lbl lsize s c fs =>
  ∃ c₀ fs₀, I lbl lsize s c₀ fs₀ ∧ FrameRun p (c₀, fs₀) (c, fs)

theorem IRun.of {I : InvS} {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : I lbl lsize s c fs) : IRun p I lbl lsize s c fs :=
  ⟨c, fs, h, .refl _⟩

/-- **A pair whose source has a pending frame run into the fragment**, not
at `main`'s return (an `OutS.frame` row's landing, or an `OutS.pre` row's
with no run), and not at a buffer allocation. -/
def PendN (p : Prog) (I : InvS) : InvS := fun lbl lsize s c fs =>
  (fs = [] → ∀ a, c.term ≠ .ret a) ∧ (∀ x a τ e, c.term ≠ .let_ x (.newBuf a τ) e) ∧ Pend p (I lbl lsize) s c fs

/-- The environments of a control with frames, innermost first
(`frameEnvs`). -/
def envsOf (c : Ctl) (fs : List TermRun.Frame) : List TermRun.Env := c.env :: fs.map (·.env)

/-- The terms of a control with frames (`frameTerms`). -/
def termsOf (c : Ctl) (fs : List TermRun.Frame) : List Expr := c.term :: fs.map (·.body)

/-- The variables each frame still reads (`frameFv`). -/
def fvOf (c : Ctl) (fs : List TermRun.Frame) : List (List String) :=
  exprFv c.term :: fs.map fun f => (exprFv f.body).filter (· != f.x)

/-- **Every frame's environment is placed** in the target state `s`
(`Placed` per frame `d`, in the order of `frameEnvs`): each placed word
represented, every word of a variable the frame still reads placed
(`frameFv`), an immediate only where the layout's table has it at the
frame's term (`frameTerms`). -/
def PlacedS (Λ : Scc.Sem.Layout) (lbl : Lbl) (s : State) (c : Ctl) (fs : List TermRun.Frame) : Prop :=
  ∃ envm : Nat → String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId),
    (∀ d env, (envsOf c fs)[d]? = some env → ∀ x ty ws, TermRun.lookupE env x = some (ty, ws) →
      ∀ k wd wp, ws[k]? = some wd → envm d x k = some wp → WordPlaceRep (machine (kernel 1)) lbl s wp wd.val) ∧
    (∀ d env xs, (envsOf c fs)[d]? = some env → (fvOf c fs)[d]? = some xs → ∀ x ∈ xs, ∀ ty ws,
      TermRun.lookupE env x = some (ty, ws) → ∀ k < ws.length, ∃ pl, envm d x k = some pl) ∧
    (∀ d e x k n, (termsOf c fs)[d]? = some e → envm d x k = some (.imm n) → Λ.imms e x k = some n)

/-- **One frame placed is every frame placed** at depth 0. -/
theorem PlacedS.ofNil {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} (h : Placed Λ lbl s c) :
    PlacedS Λ lbl s c [] := by
  obtain ⟨envm, hrep, htot, himm⟩ := h
  refine ⟨fun d => if d = 0 then envm else fun _ _ => none, ?_, ?_, ?_⟩
  · intro d env hd x ty ws hx k wd wp hwd hwp
    rcases d with _ | d
    · simp only [envsOf, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      exact hrep x ty ws hx k wd wp hwd hwp
    · simp [envsOf] at hd
  · intro d env xs hd hxs x hx ty ws hl k hk
    rcases d with _ | d
    · simp only [envsOf, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at hd
      simp only [fvOf, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at hxs
      subst hd hxs
      exact htot x hx ty ws hl k hk
    · simp [envsOf] at hd
  · intro d e x k n hd hx
    rcases d with _ | d
    · simp only [termsOf, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      exact himm x k n hx
    · simp at hx

/-- **The memory side at the frames `fs`**: `msOf` with the words owned at
`fs`, and a pair placed for `main`'s exit (`MainExit`) only at depth 0. -/
def msOfS (Λ : Scc.Sem.Layout) (μ : Marks) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop) (own : OwnS)
    (lbl : Lbl) (lsize : Lsize) (fs : List TermRun.Frame) : MemSide isaLSE2 :=
  MemSide.ofLabels rd lbl lsize (some abi) G (own := (own · fs))
    (mp := fun L w => Kernel.mapped (K0 Λ) w L = true ∧ (w = true → LocIn Λ.shared L))
    (abortAt := fun s => ∃ k a, μ.abortAt k = some a ∧ pcOf s = a) (pl := fun s c => fs = [] ∧ Placed Λ lbl s c)

/-- **The node obligations at any depth** (`Nodes` with the frames): `out`,
every pair off the take site takes an `OutS` row into the fragment, with a
pending frame run (`Pend`, as `SegWS`'s rows), under the memory side at the
frames (`msOfS`); `noRet`, no pair at depth 0 is at
`ret`; `cell` and `noAlloc` (the load and store rows access single-word
cells, no buffer allocation) at every pair a frame run reaches
(`IRun`); `noSite`, `mapped`, `svc` as in `Nodes`; `place`, every frame's
environment placed (`PlacedS`); `ownRun`, a frame run from or into the
fragment at a state keeps the words owned there (the memory is unchanged;
the producer's burden: a call or return at a state changes the frames from
`F` to `fr :: F` or back, and `own` must agree on both, e.g. owning the
words of every frame of the stack, not only the innermost);
`ownInstr`, `ownSys`, `ownTake`, the words owned at the row's frames kept
as in `Nodes`. -/
structure NodesS (Λ : Scc.Sem.Layout) (p : Prog) (μ : Marks) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : OwnS) (I : InvS) : Prop where
  out : ∀ lbl lsize s c fs, I lbl lsize s c fs → (∀ a, μ.site .take = some a → pcOf s ≠ a) →
    OutS p lbl (msOfS Λ μ rd G own lbl lsize) (Pend p (I lbl lsize)) s c fs
  noRet : ∀ lbl lsize s c, I lbl lsize s c [] → ∀ a, c.term ≠ .ret a
  cell : ∀ lbl lsize s c fs, IRun p I lbl lsize s c fs → ∀ x a e ty w,
    (c.term = .let_ x (.load true a) e ∨ ∃ b, c.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c.env a = some (ty, [w]) → OneCellTy ty
  noSite : ∀ lbl lsize s c fs, I lbl lsize s c fs → ∀ a, μ.site .release = some a → pcOf s ≠ a
  mapped : ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
    ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e
  place : ∀ lbl lsize s c fs, I lbl lsize s c fs → PlacedS Λ lbl s c fs
  svc : ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = true →
    ∃ imm sz, Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .SVC imm⟩) sz
  noAlloc : ∀ lbl lsize s c fs, IRun p I lbl lsize s c fs → ∀ x a τ e, c.term ≠ .let_ x (.newBuf a τ) e
  ownRun : ∀ lbl lsize s c fs c' fs', FrameRun p (c, fs) (c', fs') →
    (I lbl lsize s c fs ∨ I lbl lsize s c' fs') → own s fs' = own s fs
  ownInstr : ∀ lbl lsize s c fs, IRun p I lbl lsize s c fs → abi.atSys s = false → ∀ tree,
    isaLSE2.exec s = some tree → OwnTree (own · fs) (own s fs) tree
  ownSys : ∀ lbl lsize s c fs, IRun p I lbl lsize s c fs → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call,
      own s' fs = own s fs
  ownTake : ∀ lbl lsize s c fs, I lbl lsize s c fs → ∀ a, μ.site .take = some a → pcOf s = a →
    ∀ m, own (abi.skip (abi.setDmem s m)) fs = own s fs

/-- **Every frame's environment is small** (`EnvSmall`): the current one and
each suspended frame's. -/
def EnvSmallS (env : TermRun.Env) (fs : List TermRun.Frame) : Prop :=
  EnvSmall env ∧ ∀ f ∈ fs, EnvSmall f.env

/-- **The abort path at any depth** (`AbortPath` with the frames): a pair at
a resolved abort site is at the `writeErr` site in the phase `Ab`, at the
`overflow` site about to overflow with every frame's environment small
(`EnvSmallS`), or at the `heap` site about to allocate past the arena's
`cells` (`HeapReady`) from every heap use `old` within them that the
counter word `ctr`, if held, holds (`PreJ`'s heap clause gives the source
configuration's `heapUse`); an `exit_group` there has the abort status.
`instr`, `sys`, `take` as in `AbortPath`. -/
structure AbortPathS (μ : Marks) (I : InvS) (Ab : State → Prop) (cells ctr : Nat) : Prop where
  at_ : ∀ lbl lsize s c fs, I lbl lsize s c fs → ∀ k a, μ.abortAt k = some a → pcOf s = a →
    ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
      (k = .heap ∧ ∀ old, ((∃ x a τ e, c.term = .let_ x (.newBuf a τ) e) →
        old ≤ cells ∧ ∀ w, c.hold = some (ctr, w) → w = TermRun.cst (.num old)) → HeapReady cells old c)) ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus
  instr : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ab s → abi.atSys s = false → ∀ tree,
    isaLSE2.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ab s')
  sys : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ab s → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, Ab s' →
      ∃ fd buf n, call = .write fd buf n ∧ ∀ r, abi.ret s r = s' → Refusal n r
  take : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ab s → ∀ a, μ.site .take = some a → pcOf s = a →
    ∀ m, ¬ Ab (abi.skip (abi.setDmem s m))

/-- **The take path at any depth** (`TakePath` with the frames; after the
take the source takes a frame run, as after `SegWS`'s outside move,
`KOutS`). -/
structure TakePathS (Λ : Scc.Sem.Layout) (p : Prog) (μ : Marks) (I : InvS) (rS : Range) (Tk : State → Prop) :
    Prop where
  site : ∀ lbl lsize s c fs, I lbl lsize s c fs → ∀ a, μ.site .take = some a → pcOf s = a →
    ¬ Tk s ∧ (∃ sz, Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .NOP⟩) sz) ∧ abi.atSys s = false ∧
      Kernel.siteRange abi s = rS ∧
      rS.Sub Λ.stackPool ∧ 0 < rS.size ∧ Λ.rodata.Disjoint Λ.stackPool ∧
      ∀ pm, ∃ c' fs', FrameRun p (c, fs) (c', fs') ∧
        I lbl lsize (abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) rS))) c' fs' ∧
        Tk (abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) rS)))
  instr : ∀ lbl lsize s c fs, I lbl lsize s c fs → Kernel.siteAt abi μ s = none → abi.atSys s = false →
    ∀ tree, isaLSE2.exec s = some tree →
    tree.AllInv (fun _ _ => True) (fun s' => Tk s' ↔ Tk s)
  sys : ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, (Tk s' ↔ Tk s)
  owned : ∀ lbl lsize s c fs, I lbl lsize s c fs → Tk s → Owned Λ rS s

/-- **The source side's safety at any depth** (`SrcSafe` over the pairs a
frame run reaches from the fragment, `IRun`, at thread 0's frames). The next
label's freshness at a buffer allocation is not a source fact (a promise may
place it); `PreJ` carries it as `FreshInv` instead. -/
structure SrcSafeS (P : SrcSem.SrcParams) (p : Prog) (I : InvS) : Prop where
  cell : ∀ tr s th, (SrcSem.source P p).Reach tr s → s.ths[0]? = some th → ∀ lbl lsize st hd,
    IRun p I lbl lsize st ⟨th.term, th.env, hd⟩ th.stack →
    ∀ x a e ty w sa, (th.term = .let_ x (.load true a) e ∨ ∃ b, th.term = .let_ x (.store true a b none) e) →
      TermRun.evalAt th.env a = some (ty, [w]) → w.val = .loc sa 0 →
      ∃ (k : Nat) (m : WeakMem.Msg), s.mem[k]? = some m ∧ m.loc = sa
  xchg : ∀ tr s th, (SrcSem.source P p).Reach tr s → s.ths[0]? = some th → ∀ lbl lsize st hd,
    IRun p I lbl lsize st ⟨th.term, th.env, hd⟩ th.stack → ∀ x sa u v e, XchgSite ⟨th.term, th.env, hd⟩ x sa u v e →
      ∃ (k : Nat) (m : WeakMem.Msg), s.mem[k]? = some m ∧ m.loc = sa

/-- **The source's latest word at a load trigger is a number** at any depth
(`SrcSafeS.num`, kept apart from `SrcSafeS` so that its trigger is a
parameter): from thread 0 at a control `c1` a frame run reaches from the
fragment (`IRun`), with `c1`'s term and environment thread 0's, every local
run to a control `c'` that `Ld` marks as a load of word `j` of label `l`
finds the source's latest message at `⟨l, j⟩` a number, when thread 0
has no outstanding promise. `Ld` names the
loads (e.g. `print`'s element load, on the H7c path); with `Ld` false it
holds (`SrcNumS.none`). The consumer of the byte output (`byteOut_emit`)
takes its `hnum` from it. -/
def SrcNumS (P : SrcSem.SrcParams) (p : Prog) (I : InvS) (Ld : Ctl → WeakMem.AllocLabel → Nat → Prop) : Prop :=
  ∀ tr s th, (SrcSem.source P p).Reach tr s → s.ths[0]? = some th →
    th.promises = [] → ∀ lbl lsize st (c1 : Ctl),
    c1.term = th.term → c1.env = th.env → IRun p I lbl lsize st c1 th.stack →
    ∀ c' l j, LocalRun p c1 c' → Ld c' l j →
      ∃ (k : Nat) (m : WeakMem.Msg) (n : Nat), MemRel.SLatest s.mem ⟨l, j⟩ k ∧ s.mem[k]? = some m ∧ m.val = .num n

/-- `SrcNumS` with no load marked. -/
theorem SrcNumS.none {P : SrcSem.SrcParams} {p : Prog} {I : InvS} : SrcNumS P p I (fun _ _ _ => False) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => h.elim

/-- `SrcNumS` is antitone in the loads marked. -/
theorem SrcNumS.mono {P : SrcSem.SrcParams} {p : Prog} {I : InvS} {Ld Ld' : Ctl → WeakMem.AllocLabel → Nat → Prop}
    (h : SrcNumS P p I Ld) (hL : ∀ c l j, Ld' c l j → Ld c l j) : SrcNumS P p I Ld' :=
  fun tr s th hr h0 hp lbl lsize st c1 ht he hI c' l j hlr hl =>
    h tr s th hr h0 hp lbl lsize st c1 ht he hI c' l j hlr (hL _ _ _ hl)

/-! ## The relation -/

/-- **The heap counter at a buffer allocation**: the source configuration's
heap use is within the arena's `cells`, and a hold of the counter word
`ctr` holds it. -/
def HeapCtr (cells ctr : Nat) (s : TermRun.Cfg) (c : Ctl) : Prop :=
  (∃ x a τ e, c.term = .let_ x (.newBuf a τ) e) →
    heapUse s ≤ cells ∧ ∀ w, c.hold = some (ctr, w) → w = TermRun.cst (.num (heapUse s))

/-- **Before the exit, over a fragment `J`** (`Pre` with the frames): the
source thread's stack is `J`'s frames, and the words owned are those at
them; at a buffer allocation the source configuration's heap use is within
the arena's `cells` and is the count the counter word `ctr` holds, if held
(`HeapCtr`); thread 0's labels from its allocation count on are unplaced
(`FreshInv`). -/
def PreJ (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (J : InvS)
    (rS : Range) (Tk : State → Prop) (μ : Marks) (cells ctr : Nat) (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ (th : Thread isaLSE2) (th0 : TermRun.TTh) (j : Nat) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
    (hl : List (Nat × Range)) (pm : _root_.Mem 64) (hd : Option (Nat × TermRun.Word)),
    t.1.threads = #[th] ∧ (∃ E : Entry, t.2 = KS E Λ j hl pm) ∧ (∀ a, Kernel.byte pm a = 0) ∧ HeldOk Λ rS Tk th.st hl ∧
    WrOk th j ∧
    CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ t.2 0) 0 th t.1.mem ∧
    s.ths = #[th0] ∧ th0.σs = [] ∧ th0.promises = [] ∧
    J lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack ∧ HoldInv lbl lsize s.mem hd ∧ WideSt th.st ∧
    th.Bnd t.1.mem.last ∧ Inv1 Λ lbl lsize ts th t.1.mem s.mem ∧
    OwnMsgs t.1.mem ∧ MemIn Λ t.1.mem ∧ MemFits t.1.mem ∧ MemInv G t.1.mem ∧
    ExtRows.OwnOk (own th.st th0.stack) t.1.mem th.prom ∧ HeapCtr cells ctr s ⟨th0.term, th0.env, hd⟩ ∧
    AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc ∧ ∃ tr, (SrcSem.source P p).Reach tr s

/-- **Before the exit** at any depth: `PreJ` over the fragment. -/
abbrev PreS (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (I : InvS)
    (rS : Range) (Tk : State → Prop) (μ : Marks) (cells ctr : Nat) (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  PreJ Λ P p G own I rS Tk μ cells ctr t s

/-- **After the exit** at any depth (`Post` with the frames: an abort may
end the process inside a callee): every frame's environment placed. -/
def PostS (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (rS : Range) (Tk : State → Prop)
    (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ (th : Thread isaLSE2) (th0 : TermRun.TTh) (j : Nat) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
    (hl : List (Nat × Range)) (pm : _root_.Mem 64) (o : Outcome),
    t.1.threads = #[th] ∧ (∃ E : Entry, t.2 = { KS E Λ j hl pm with exited := some o }) ∧ (∀ a, Kernel.byte pm a = 0) ∧
    HeldOk Λ rS Tk th.st hl ∧
    s.ths = #[th0] ∧ th0.σs = [] ∧ th0.promises = [] ∧
    PlacedS Λ lbl th.st (Ctl.of th0) th0.stack ∧ Inv1 Λ lbl lsize ts th t.1.mem s.mem ∧ OwnMsgs t.1.mem ∧
    MemIn Λ t.1.mem ∧ ∃ tr, (SrcSem.source P p).Reach tr s

/-- **The relation** at any depth. -/
def RS (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (I : InvS)
    (rS : Range) (Tk : State → Prop) (μ : Marks) (cells ctr : Nat) (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  PreS Λ P p G own I rS Tk μ cells ctr t s ∨ PostS Λ P p rS Tk t s

/-! ## Source runs of the one thread -/

/-- **A frame run of the one source thread** (no type variables, no
promises), not from or to `main`'s return, is a run with no event. -/
theorem frun_one (hP : HookOK P p) {q q' : Ctl × List TermRun.Frame} (h : FrameRun p q q')
    {s : TermRun.Cfg} {th0 : TermRun.TTh} (hs0 : s.ths = #[th0]) (ht : th0.term = q.1.term) (he : th0.env = q.1.env)
    (hσ : th0.σs = []) (hst : th0.stack = q.2) (hp : th0.promises = []) (hr : q.2 = [] → ∀ a, q.1.term ≠ .ret a)
    (hr' : q'.2 = [] → ∀ a, q'.1.term ≠ .ret a) :
    (SrcSem.source P p).Run s []
      { s with ths := #[{ th0 with term := q'.1.term, env := q'.1.env, stack := q'.2 }] } := by
  have h0 : s.ths[0]? = some th0 := by rw [hs0]; rfl
  have := h.run_source_nil hP h0 ht he hσ hst hp hr hr'
  rwa [set_one hs0] at this

/-- A control at `ret` takes no local run but the empty one. -/
theorem noRet_of_run {c c' : Ctl} (h : LocalRun p c c') (hr : ∀ a, c'.term ≠ .ret a) : ∀ a, c.term ≠ .ret a := by
  cases h with
  | refl => exact hr
  | step hs _ => exact localStep_not_ret hs

/-- A frame run keeps `HoldInv`: a local step holds the same or nothing, a
call or return holds nothing. -/
theorem holdInv_frameRun {lbl : Lbl} {lsize : Lsize} {sm : WeakMem.Memory} {q q' : Ctl × List TermRun.Frame}
    (hr : FrameRun p q q') (h : HoldInv lbl lsize sm q.1.hold) : HoldInv lbl lsize sm q'.1.hold := by
  induction hr with
  | refl => exact h
  | step hs _ ih =>
    apply ih
    cases hs with
    | loc hs => exact holdInv_run (.step hs.toLocalStep (.refl _)) h
    | call => trivial
    | ret => trivial

/-- **The source store of the store row at any depth** (`src_store_step`
with the continuation off `ret` only at depth 0, the allocation count kept). -/
theorem src_store_stepS (hP : HookOK P p) {c : TermRun.Cfg}
    {th : TermRun.TTh} {x : String} {a b : At} {e : Expr} {ty tb : Ty} {pw wb : TermRun.Word}
    {sa : WeakMem.Address} (h0 : c.ths[0]? = some th) (hp : th.promises = [])
    (ht : th.term = .let_ x (.store true a b none) e) (hea : TermRun.evalAt th.env a = some (ty, [pw]))
    (hpw : pw.val = .loc sa 0) (hcell : OneCellTy ty) (heb : TermRun.evalAt th.env b = some (tb, [wb]))
    (hr : th.stack = [] → ∀ a, e ≠ .ret a) :
    ∃ (th' : TermRun.TTh) (mv : Nat), (SrcSem.source P p).step 0 c []
        { c with mem := c.mem.push ⟨sa, wb.val, mv⟩, ths := c.ths.set! 0 th' } ∧
      th'.term = e ∧ th'.env = (x, .unit, []) :: th.env ∧ th'.promises = [] ∧ th'.σs = th.σs ∧
      th'.stack = th.stack ∧ th'.nalloc = th.nalloc := by
  obtain ⟨μ', u, hc, hu⟩ := hcell
  obtain ⟨th', mv, hm, hte, hen, hp', hσ, hst, hna⟩ :=
    SrcMemN.src_store_step_cfgN (p := p) (k := P.k) (arch := P.arch) h0 ht hea heb hpw hc hu hp
  have hlt : 0 < c.ths.size := (Array.getElem?_eq_some_iff.mp h0).1
  have h0' : ({ c with mem := c.mem.push ⟨sa, wb.val, mv⟩, ths := c.ths.set! 0 th' } : TermRun.Cfg).ths[0]? =
      some th' := by simp [hlt]
  refine ⟨th', mv, src_step_of_threadSteps hP hm h0' hp' (mainExit_of_not_ret h0 ?_)
    (mainExit_of_pair h0' fun h a' => hte ▸ hr (hst ▸ h) a'), hte, hen, hp', hσ, hst, hna⟩
  intro a' h; rw [ht] at h; cases h

/-- **The source load of the load row at any depth** (`src_load_step` with
the continuation off `ret` only at depth 0, the allocation count kept). -/
theorem src_load_stepS (hP : HookOK P p) {c : TermRun.Cfg}
    {th : TermRun.TTh} {x : String} {a : At} {e : Expr} {ty : Ty} {pw : TermRun.Word} {sa : WeakMem.Address}
    {j : Nat} {m : WeakMem.Msg} (h0 : c.ths[0]? = some th) (hp : th.promises = [])
    (ht : th.term = .let_ x (.load true a) e) (hea : TermRun.evalAt th.env a = some (ty, [pw]))
    (hpw : pw.val = .loc sa 0) (hcell : OneCellTy ty) (hj : MemRel.SLatest c.mem sa j) (hm : c.mem[j]? = some m)
    (hr : th.stack = [] → ∀ a, e ≠ .ret a) :
    ∃ th' : TermRun.TTh, (SrcSem.source P p).step 0 c [] { c with ths := c.ths.set! 0 th' } ∧
      th'.term = e ∧ th'.env = (x, loadTy ty, [⟨m.val, m.view, j⟩]) :: th.env ∧ th'.promises = [] ∧
      th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc := by
  obtain ⟨μ', u, hc, hu⟩ := hcell
  obtain ⟨th', hst, hte, hen, hp', hσ, hsk, hna⟩ :=
    SrcMemN.src_load_step_cfgN (p := p) (k := P.k) (arch := P.arch) h0 ht hea hpw hc hu hj hm
  have hlt : 0 < c.ths.size := (Array.getElem?_eq_some_iff.mp h0).1
  have h0' : ({ c with ths := c.ths.set! 0 th' } : TermRun.Cfg).ths[0]? = some th' := by simp [hlt]
  refine ⟨th', src_step_of_threadSteps hP hst h0' (hp'.trans hp) (mainExit_of_not_ret h0 ?_)
    (mainExit_of_pair h0' fun h a' => hte ▸ hr (hsk ▸ h) a'), hte, hen, hp'.trans hp, hσ, hsk, hna⟩
  intro a' h; rw [ht] at h; cases h

/-- **The source exchange at any depth** (`src_swap_step` with the
continuation off `ret` only at depth 0, the allocation count kept). -/
theorem src_swap_stepS (hP : HookOK P p) {c : TermRun.Cfg} {th : TermRun.TTh} {x : String}
    {sa : WeakMem.Address} {u : Ty} {v : At} {e : Expr} {tv : Ty} {wv : TermRun.Word} {j : Nat} {m : WeakMem.Msg}
    (h0 : c.ths[0]? = some th) (hp : th.promises = []) (hs : XchgSite ⟨th.term, th.env, none⟩ x sa u v e)
    (hev : TermRun.evalAt th.env v = some (tv, [wv])) (hj : MemRel.SLatest c.mem sa j) (hm : c.mem[j]? = some m)
    (hr0 : ∀ a, th.term ≠ .ret a) (hr : th.stack = [] → ∀ a, e ≠ .ret a) :
    ∃ (th' : TermRun.TTh) (mv : Nat), (SrcSem.source P p).step 0 c []
        { c with mem := c.mem.push ⟨sa, wv.val, mv⟩, ths := c.ths.set! 0 th' } ∧
      th'.term = e ∧ th'.env = (x, u, [⟨m.val, m.view, j⟩]) :: th.env ∧ th'.promises = [] ∧ th'.σs = th.σs ∧
      th'.stack = th.stack ∧ th'.nalloc = th.nalloc := by
  obtain ⟨th', mv, hst, hte, hen, hp', hσ, hsk, hna⟩ :=
    SrcMemN.src_swap_step_cfgN (p := p) (k := P.k) (arch := P.arch) h0 hs hev hp hj hm
  have hlt : 0 < c.ths.size := (Array.getElem?_eq_some_iff.mp h0).1
  have h0' : ({ c with mem := c.mem.push ⟨sa, wv.val, mv⟩, ths := c.ths.set! 0 th' } : TermRun.Cfg).ths[0]? =
      some th' := by simp [hlt]
  exact ⟨th', mv, src_step_of_threadSteps hP hst h0' hp' (mainExit_of_not_ret h0 hr0)
    (mainExit_of_pair h0' fun h a' => hte ▸ hr (hsk ▸ h) a'), hte, hen, hp', hσ, hsk, hna⟩

/-- An exchange site is a `let`, not at `ret`. -/
theorem xchgSite_not_ret {c : Ctl} {x : String} {sa : WeakMem.Address} {u : Ty} {v : At} {e : Expr}
    (h : XchgSite c x sa u v e) : ∀ a, c.term ≠ .ret a := by
  intro a' ha
  rcases h with ⟨-, ⟨_, _, _, _, h, -⟩ | ⟨_, _, _, _, _, _, _, _, _, h, -⟩⟩ <;> rw [ha] at h <;> cases h

/-- Two runs with no event. -/
theorem run_trans0 {s s₁ s₂ : TermRun.Cfg} (h₁ : (SrcSem.source P p).Run s [] s₁)
    (h₂ : (SrcSem.source P p).Run s₁ [] s₂) : (SrcSem.source P p).Run s [] s₂ := by
  have := Scc.Sem.LRun.trans h₁ h₂; rw [List.append_nil] at this; exact this

/-- `HeapCtr` holds off a buffer allocation. -/
theorem heapCtr_of {cells ctr : Nat} {s : TermRun.Cfg} {c : Ctl}
    (h : ∀ x a τ e, c.term ≠ .let_ x (.newBuf a τ) e) : HeapCtr cells ctr s c :=
  fun ⟨x, a, τ, e, he⟩ => absurd he (h x a τ e)

/-- **A row's state facts from an `OutS` row**: some `Out` row at the same
state (an `OutS.frame` row as a silent one), for the facts about the
target alone. -/
theorem OutS.out {lbl : Lbl} {ms : List TermRun.Frame → MemSide isaLSE2} {X : FragS isaLSE2} {s : State} {c : Ctl}
    {fs : List TermRun.Frame} (h : OutS p lbl ms X s c fs) :
    ∃ (c₁ : Ctl) (fs₁ : List TermRun.Frame) (Y : Frag isaLSE2), Out p lbl (ms fs₁) Y s c₁ := by
  cases h with
  | pre c₁ fs₁ _ h => exact ⟨c₁, fs₁, _, h⟩
  | frame s' c' fs' he _ _ => exact ⟨c, fs, fun _ _ => True, .silent s' c he (.refl c) trivial⟩

variable {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : OwnS}
  {cells ctr : Nat}

/-- **The row of a pair of the fragment**, normalised: the source takes a
frame run to `(c₁, fs₁)` (a pair `IRun` reaches, owning what the pair owns),
from which the instruction is an `Out` row landing in `PendN` at `fs₁`
(an `OutS.frame` row as a silent row with its frame run pending). -/
theorem NodesS.row (hN : NodesS Λ p μ rd G own I) {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl}
    {fs : List TermRun.Frame} (hI : I lbl lsize s c fs) (hnt : ∀ a, μ.site .take = some a → pcOf s ≠ a) :
    ∃ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) ∧ own s fs₁ = own s fs ∧
      Out p lbl (msOfS Λ μ rd G own lbl lsize fs₁) (fun s' c' => PendN p I lbl lsize s' c' fs₁) s c₁ := by
  cases hN.out _ _ _ _ _ hI hnt with
  | pre c₁ fs₁ hr h =>
    refine ⟨c₁, fs₁, hr, hN.ownRun _ _ _ _ _ _ _ hr (.inl hI), h.mono fun s' c' h' => ⟨?_, ?_, h'⟩⟩
    · rintro h0 a hc
      obtain ⟨c'', fs'', hr', h''⟩ := h'
      cases hr'.eq_of_stuck (.inr ⟨h0, a, hc⟩)
      exact hN.noRet _ _ _ _ (h0 ▸ h'') a hc
    · rintro x a τ e hc
      obtain ⟨c'', fs'', hr', h''⟩ := h'
      cases hr'.eq_of_stuck (.inl ⟨x, a, τ, e, hc⟩)
      exact hN.noAlloc _ _ _ _ _ (IRun.of h'') x a τ e hc
  | frame s' c' fs' he hr hx =>
    obtain ⟨c'', fs'', hr', hx⟩ := hx
    refine ⟨c, fs, .refl _, rfl, .silent s' c he (.refl c)
      ⟨?_, hN.noAlloc _ _ _ _ _ (IRun.of hI), c'', fs'', hr.trans hr', hx⟩⟩
    exact fun h0 => hN.noRet _ _ _ _ (h0 ▸ hI)

/-- The pair a row starts from is one a frame run reaches. -/
theorem IRun.trans {lbl : Lbl} {lsize : Lsize} {s : State} {c c₁ : Ctl} {fs fs₁ : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hr : FrameRun p (c, fs) (c₁, fs₁)) : IRun p I lbl lsize s c₁ fs₁ :=
  ⟨c, fs, hI, hr⟩

/-- A pair at a system call is off the take site. -/
theorem TakePathS.off_sys {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {lbl : Lbl}
    {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame} (hI : I lbl lsize s c fs)
    (hs : abi.atSys s = true) : ∀ a, μ.site .take = some a → pcOf s ≠ a := fun a ha hpc => by
  have h := (hT.site _ _ _ _ _ hI a ha hpc).2.2.1
  rw [hs] at h; cases h

/-- **The row at a system call** is `Out.sys` after a frame run (an
`OutS.frame` row is silent, but the instruction at an `svc` cell faults),
each successor's source after a frame run (the row's local run, then the
landing's pending run). -/
theorem NodesS.sysRow (hN : NodesS Λ p μ rd G own I) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame} (hI : I lbl lsize s c fs)
    (hs : abi.atSys s = true) :
    ∃ c₁ fs₁ call, FrameRun p (c, fs) (c₁, fs₁) ∧
      Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧
      SysOk p (msOfS Λ μ rd G own lbl lsize fs₁) s c₁ call ∧
      ∀ s' ∈ Kernel.certSuccs abi s call, ∃ c' fs', FrameRun p (c₁, fs₁) (c', fs') ∧ I lbl lsize s' c' fs' := by
  obtain ⟨imm, sz, hc⟩ := hN.svc _ _ _ _ _ hI hs
  cases hN.out _ _ _ _ _ hI (hT.off_sys hI hs) with
  | pre c₁ fs₁ hr h =>
    obtain ⟨K, call, hK, -, hd, hok, hx⟩ := out_sys hc h (fun _ h => False.elim h)
    cases hK
    refine ⟨c₁, fs₁, call, hr, hd, hok, fun s' hs' => ?_⟩
    obtain ⟨c', hlr, c'', fs'', hr', h'⟩ := hx s' hs'
    exact ⟨c'', fs'', (FrameRun.ofLocal hlr fs₁).trans hr', h'⟩
  | frame s' c' fs' he _ _ =>
    rw [Kraken.Promising.Lower.A64.exec_svc hc] at he; cases he

/-- **A system call of the fragment is supported** (`Nodes.sysOk`). -/
theorem NodesS.sysOk (hN : NodesS Λ p μ rd G own I) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame} (hI : I lbl lsize s c fs)
    (hs : abi.atSys s = true) :
    ∃ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧ call ≠ .exit ∧
      (∀ st tl, call ≠ .clone st tl) ∧ ∀ fd buf n, call = .write fd buf n → fd ≠ 1 := by
  obtain ⟨c₁, fs₁, call, -, hd, ⟨hnx, hcl, hfd, -⟩, -⟩ := hN.sysRow hT hI hs
  exact ⟨call, hd, hnx, hcl, hfd⟩

/-- A pair of the fragment off the take site is at no transfer site. -/
theorem no_siteS (hN : NodesS Λ p μ rd G own I) {t : T.M.Cfg} {th : Thread isaLSE2} {lbl : Lbl} {lsize : Lsize}
    {c : Ctl} {fs : List TermRun.Frame} (ht : t.1.threads[0]? = some th) (hI : I lbl lsize th.st c fs)
    (hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a) : ∀ k, ¬ T.M.AtSite μ k t 0 := by
  rintro k ⟨a, ha, t2, ht2, hpc⟩
  cases (show some t2 = some th from ht2.symm.trans ht)
  cases k
  · exact hnt a ha hpc
  · exact hN.noSite _ _ _ _ _ hI a ha hpc

/-- A pair of the fragment off the take site is off the certification
semantics' transfer sites. -/
theorem siteAt_noneS (hN : NodesS Λ p μ rd G own I) {s : State} {lbl : Lbl} {lsize : Lsize} {c : Ctl}
    {fs : List TermRun.Frame} (hI : I lbl lsize s c fs) (hnt : ∀ a, μ.site .take = some a → pcOf s ≠ a) :
    Kernel.siteAt abi μ s = none :=
  Kernel.siteAt_eq_none_iff.mpr ⟨fun h => hnt _ h rfl, fun h => hN.noSite _ _ _ _ _ hI _ h rfl⟩

/-- **The step at the take site is the take** (`step_take`). -/
theorem step_takeS (hN : NodesS Λ p μ rd G own I) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    {t t' : T.M.Cfg} {th : Thread isaLSE2} {lbl : Lbl} {lsize : Lsize} {c : Ctl} {fs : List TermRun.Frame}
    {es : List Ev} {a : Nat}
    (ht : t.1.threads[0]? = some th) (hI : I lbl lsize th.st c fs) (ha : μ.site .take = some a)
    (hpc : pcOf th.st = a) (hs : T.M.Step μ 0 t es t') :
    es = [] ∧ t' = (t.1.withThread 0
        { th with st := abi.skip (abi.setDmem th.st (Kernel.copyRange t.2.pmem (abi.dmem th.st) rS)) } t.1.mem,
      { t.2 with held := (0, rS) :: t.2.held, pmem := Kernel.eraseRange t.2.pmem rS }) := by
  obtain ⟨-, -, hsys, hsr, -⟩ := hT.site _ _ _ _ _ hI a ha hpc
  have hat : T.M.AtSite μ .take t 0 := ⟨a, ha, th, ht, hpc⟩
  have hnr : ¬ T.M.AtSite μ .release t 0 := fun ⟨a', ha', t2, ht2, hpc'⟩ => by
    cases (show some t2 = some th from ht2.symm.trans ht)
    exact hN.noSite _ _ _ _ _ hI a' ha' hpc'
  obtain ⟨hes, hx⟩ := Kernel.step_at_take ht hsys hat hnr hs
  refine ⟨hes, ?_⟩
  subst hsr
  unfold Kernel.takeStep at hx
  erw [ht] at hx
  simp only at hx
  split at hx
  · exact (Option.some.inj hx).symm
  · cases hx

/-- A pair of the fragment does not spawn (`NodesS.sysOk`: no `clone`). -/
theorem no_spawnS (hN : NodesS Λ p μ rd G own I) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    {t t' : T.M.Cfg} {th : Thread isaLSE2} {lbl : Lbl} {lsize : Lsize} {c : Ctl} {fs : List TermRun.Frame}
    (ht : t.1.threads[0]? = some th) (hI : I lbl lsize th.st c fs) : ¬ (A64.kernel 1).spawn μ 0 t t' := by
  rintro ⟨jj, r, h, -⟩
  unfold Kernel.spawnStep at h
  erw [ht] at h
  simp only at h
  cases hr : Kernel.ready abi 0 t th
  · simp [hr] at h
  · obtain ⟨call, hd, -, hcl, -⟩ := hN.sysOk hT hI (atSys_of_ready hr)
    simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false] at h
    rw [show Kernel.callOf abi th = some call from hd] at h
    cases call with
    | clone st tl => exact hcl st tl rfl
    | _ => cases h

/-- **A pending frame run is taken**: from `PreJ` over `PendN` the source
takes the pending run (not from or to `main`'s return) into the fragment,
the words owned unchanged (`ownRun`), the hold kept or dropped. -/
theorem pend_run (hP : HookOK P p) (hN : NodesS Λ p μ rd G own I) {rS : Range}
    {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    (h : PreJ Λ P p G own (PendN p I) rS Tk μ cells ctr t s) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreS Λ P p G own I rS Tk μ cells ctr t s' := by
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, hk, hz, hh, hwr, hcert, hs0, hσ, hp,
    ⟨hnr, -, c₂, fs₂, hr, hI⟩, hhi, hw, hb, hinv, hown, hmi, hfi, hgi, hoo, -, hfr, tr, hreach⟩ := h
  have hrun := frun_one (q := (⟨th0.term, th0.env, hd⟩, th0.stack)) hP hr hs0 rfl rfl hσ rfl hp hnr
    (fun h0 => hN.noRet _ _ _ _ (by simp only at h0; subst h0; exact hI))
  refine ⟨_, hrun, th, { th0 with term := c₂.term, env := c₂.env, stack := fs₂ }, j, lbl, lsize, ts, hl, pm, c₂.hold,
    hth, hk, hz, hh, hwr, hcert, rfl, hσ, hp, hI, holdInv_frameRun hr hhi, hw, hb, hinv, hown, hmi, hfi, hgi, ?_,
    heapCtr_of (hN.noAlloc _ _ _ _ _ (IRun.of hI)), (by rw [TermRun.Cfg.n, hs0] at hfr; exact hfr), _, reach_run hreach hrun⟩
  show ExtRows.OwnOk (own th.st fs₂) _ _
  rw [hN.ownRun _ _ _ _ _ _ _ hr (.inr hI)]; exact hoo

/-- `PendN`'s pair is off `main`'s return. -/
theorem PendN.noRet {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : PendN p I lbl lsize s c fs) : fs = [] → ∀ a, c.term ≠ .ret a := by
  obtain ⟨h1, -⟩ := h; exact h1

/-- `PendN`'s pair is off a buffer allocation. -/
theorem PendN.noAlloc {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : PendN p I lbl lsize s c fs) : ∀ x a τ e, c.term ≠ .let_ x (.newBuf a τ) e := by
  obtain ⟨-, h1, -⟩ := h; exact h1

/-- `PendN`'s state is one of the fragment's. -/
theorem PendN.inv {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : PendN p I lbl lsize s c fs) : ∃ c' fs', I lbl lsize s c' fs' := by
  obtain ⟨-, -, c', fs', -, h⟩ := h; exact ⟨c', fs', h⟩

/-- `FreshInv` along a one-thread configuration change keeping the label
base, the capacity and the thread's allocation count. -/
theorem freshInv_one {lbl : Lbl} {s s' : TermRun.Cfg} {th0 th' : TermRun.TTh} (hs0 : s.ths = #[th0])
    (hs' : s'.ths = #[th']) (hb : s'.lbase = s.lbase) (hc : s'.cap = s.cap) (hna : th'.nalloc = th0.nalloc)
    (h : AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc) : AllocInv.FreshInv lbl s'.lbase s'.n 0 th'.nalloc := by
  rw [TermRun.Cfg.n, hs0] at h; rw [TermRun.Cfg.n, hs', hb, hc, hna]; exact h

/-- **The source at a row's control**: the frame run before a row, taken
by the one source thread (the memory, label base and allocation count
kept). -/
theorem row_src (hP : HookOK P p) {s : TermRun.Cfg} {th0 : TermRun.TTh} {c₁ : Ctl}
    {fs₁ : List TermRun.Frame} {lbl : Lbl} (hs0 : s.ths = #[th0]) (hσ : th0.σs = []) (hp : th0.promises = [])
    {hd : Option (Nat × TermRun.Word)} (hr0 : FrameRun p (⟨th0.term, th0.env, hd⟩, th0.stack) (c₁, fs₁))
    (hr : th0.stack = [] → ∀ a, th0.term ≠ .ret a) (hr1 : fs₁ = [] → ∀ a, c₁.term ≠ .ret a)
    (hfr : AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc) :
    ∃ (s₁ : TermRun.Cfg) (th1 : TermRun.TTh), (SrcSem.source P p).Run s [] s₁ ∧ s₁.ths = #[th1] ∧
      th1.term = c₁.term ∧ th1.env = c₁.env ∧ th1.stack = fs₁ ∧ th1.σs = [] ∧ th1.promises = [] ∧
      s₁.mem = s.mem ∧ AllocInv.FreshInv lbl s₁.lbase s₁.n 0 th1.nalloc :=
  ⟨_, _, frun_one hP hr0 hs0 rfl rfl hσ rfl hp hr hr1, rfl, rfl, rfl, rfl, hσ, hp, rfl,
    by rw [TermRun.Cfg.n, hs0] at hfr; exact hfr⟩

/-- **A frame run lands in `PreJ`** over any fragment `J` (`pre_local` with
the frames): the target thread replaced by `u` (its `write` count 0), the
source thread by the run's end, the hold the run's. -/
theorem pre_localJ (hP : HookOK P p) {J : InvS} {t' : T.M.Cfg} {s : TermRun.Cfg}
    {u : Thread isaLSE2} {th0 : TermRun.TTh} {lbl : Lbl} {lsize : Lsize} {ts : Nat → Option Nat} {c' : Ctl}
    {fs' : List TermRun.Frame} {rS : Range} {Tk : State → Prop} {hl : List (Nat × Range)} {pm : _root_.Mem 64}
    {hd : Option (Nat × TermRun.Word)}
    (hth : t'.1.threads = #[u]) (hk : t'.2 = KS E Λ 0 hl pm) (hz : ∀ a, Kernel.byte pm a = 0)
    (hh : HeldOk Λ rS Tk u.st hl)
    (hc : CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ t'.2 0) 0 u t'.1.mem) (hs0 : s.ths = #[th0])
    (hσ : th0.σs = []) (hp : th0.promises = []) (hJ : J lbl lsize u.st c' fs') (hw : WideSt u.st)
    (hb : u.Bnd t'.1.mem.last) (hinv : Inv1 Λ lbl lsize ts u t'.1.mem s.mem) (hown : OwnMsgs t'.1.mem)
    (hmi : MemIn Λ t'.1.mem) (hfi : MemFits t'.1.mem) (hgi : MemInv G t'.1.mem)
    (hoo : ExtRows.OwnOk (own u.st fs') t'.1.mem u.prom) (hna : ∀ x a τ e, c'.term ≠ .let_ x (.newBuf a τ) e)
    (hfr : AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc) (hre : ∃ tr, (SrcSem.source P p).Reach tr s)
    (hhi : HoldInv lbl lsize s.mem hd) (hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a)
    (hcr' : fs' = [] → ∀ a, c'.term ≠ .ret a) (hr : FrameRun p (⟨th0.term, th0.env, hd⟩, th0.stack) (c', fs')) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreJ Λ P p G own J rS Tk μ cells ctr t' s' := by
  have hrun := frun_one hP hr hs0 rfl rfl hσ rfl hp hcr hcr'
  obtain ⟨tr, hre⟩ := hre
  exact ⟨_, hrun, u, { th0 with term := c'.term, env := c'.env, stack := fs' }, 0, lbl, lsize, ts, hl, pm, c'.hold,
    hth, ⟨E, hk⟩, hz, hh, .inl rfl, hc, rfl, hσ, hp, hJ, holdInv_frameRun hr hhi, hw, hb, hinv, hown, hmi, hfi, hgi,
    hoo, heapCtr_of hna, by rw [TermRun.Cfg.n, hs0] at hfr; exact hfr, _, reach_run hre hrun⟩

/-- **A landing over `PendN` is a step of the relation**: the pending frame
run taken (`pend_run`). -/
theorem pend_land (hP : HookOK P p) (hN : NodesS Λ p μ rd G own I) {rS : Range}
    {Tk : State → Prop} {t : T.M.Cfg} {s s₂ : TermRun.Cfg} (hrun : (SrcSem.source P p).Run s [] s₂)
    (h : PreJ Λ P p G own (PendN p I) rS Tk μ cells ctr t s₂) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ RS Λ P p G own I rS Tk μ cells ctr t s' := by
  obtain ⟨s', hr, hpre⟩ := pend_run hP hN h
  exact ⟨s', run_trans0 hrun hr, .inl hpre⟩

/-- **Promises are to shared regions** at any depth (`PromShared` over
`PreS`). -/
def PromSharedS (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS)
    (I : InvS) (rS : Range) (Tk : State → Prop) (μ : Marks) (cells ctr : Nat) : Prop :=
  ∀ t s th w, PreS Λ P p G own I rS Tk μ cells ctr t s → t.1.threads = #[th] → w.tid = 0 →
    CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ t.2 0) 0 (Live.Sem.promThread th t.1.mem w)
      (t.1.mem.append w).1 →
    LocIn Λ.shared w.loc ∧ G w.loc w.val

/-! ## The steps -/

/-- **The source thread after a row's frame run** to `(c, fs)`. -/
abbrev thAt (th0 : TermRun.TTh) (c : Ctl) (fs : List TermRun.Frame) : TermRun.TTh :=
  { th0 with term := c.term, env := c.env, stack := fs }

/-- **`SrcSafeS.cell` after a row's frame run**: at the source thread the
run lands in (`thAt`), the memory unchanged. -/
theorem SrcSafeS.cell₁ (hsafe : SrcSafeS P p I) {tr : List Ev} {s : TermRun.Cfg} {th0 : TermRun.TTh} {c₁ : Ctl}
    {fs₁ : List TermRun.Frame} (hreach : (SrcSem.source P p).Reach tr { s with ths := #[thAt th0 c₁ fs₁] })
    {lbl : Lbl} {lsize : Lsize} {st : State} (hI1 : IRun p I lbl lsize st c₁ fs₁) {x : String} {a : At} {e : Expr}
    {ty : Ty} {w : TermRun.Word} {sa : WeakMem.Address}
    (ht : c₁.term = .let_ x (.load true a) e ∨ ∃ b, c₁.term = .let_ x (.store true a b none) e)
    (hev : TermRun.evalAt c₁.env a = some (ty, [w])) (hsa : w.val = .loc sa 0) :
    ∃ (k : Nat) (m : WeakMem.Msg), s.mem[k]? = some m ∧ m.loc = sa :=
  hsafe.cell tr _ (thAt th0 c₁ fs₁) hreach rfl lbl lsize st c₁.hold hI1 x a e ty w sa ht hev hsa

/-- **`SrcSafeS.xchg` after a row's frame run** (`SrcSafeS.cell₁`). -/
theorem SrcSafeS.xchg₁ (hsafe : SrcSafeS P p I) {tr : List Ev} {s : TermRun.Cfg} {th0 : TermRun.TTh} {c₁ : Ctl}
    {fs₁ : List TermRun.Frame} (hreach : (SrcSem.source P p).Reach tr { s with ths := #[thAt th0 c₁ fs₁] })
    {lbl : Lbl} {lsize : Lsize} {st : State} (hI1 : IRun p I lbl lsize st c₁ fs₁) {x : String}
    {sa : WeakMem.Address} {u : Ty} {v : At} {e : Expr} (hxs : XchgSite c₁ x sa u v e) :
    ∃ (k : Nat) (m : WeakMem.Msg), s.mem[k]? = some m ∧ m.loc = sa :=
  hsafe.xchg tr _ (thAt th0 c₁ fs₁) hreach rfl lbl lsize st c₁.hold hI1 x sa u v e hxs

/-- A pair with a pending run into the fragment has its state owned when
taken (`TakePathS.owned`). -/
theorem TakePathS.ownedN {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {lbl : Lbl}
    {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame} (h : PendN p I lbl lsize s c fs) (hk : Tk s) :
    Owned Λ rS s := by
  obtain ⟨c', fs', h'⟩ := h.inv; exact hT.owned _ _ _ _ _ h' hk

/-- **The steps before the exit at any depth** (`pre_step` with the frames):
every step from `PreS` is matched by a source run with its observable
events, landing in `RS`. A row's frame run is taken with the row's source
step; its landing's pending run after it (`pend_land`). -/
theorem pre_stepS (hP : HookOK P p) (hN : NodesS Λ p μ rd G own I) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hps : PromSharedS Λ P p G own I rS Tk μ cells ctr) (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev} (h : PreS Λ P p G own I rS Tk μ cells ctr t s)
    (hs : T.M.Step μ tid t es t') :
    ∃ s', (SrcSem.source P p).Run s (obs es) s' ∧ RS Λ P p G own I rS Tk μ cells ctr t' s' := by
  have hpre := h
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, hz, hh, hwr, hcert0, hs0, hσ, hp, hI, hhi, hw,
    hb, hinv, hown, hmi, hfi, hgi, hoo, hhc, hfr, tr, hreach⟩ := h
  obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
  obtain ⟨rfl, rfl⟩ := get_one hth ht1
  have h0 : s.ths[0]? = some th0 := by rw [hs0]; rfl
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
  · -- the take: a local run of the source
    obtain ⟨a, ha, hpc⟩ := htk
    obtain ⟨hntk, ⟨sz, hcn⟩, hsys, -, -, -, -, hrun⟩ := hT.site _ _ _ _ _ hI a ha hpc
    have hat : T.M.AtSite μ .take t 0 := ⟨a, ha, th, ht1, hpc⟩
    have hnr : ¬ T.M.AtSite μ .release t 0 := fun ⟨a', ha', t2, ht2, hpc'⟩ => by
      cases (show some t2 = some th from ht2.symm.trans ht1)
      exact hN.noSite _ _ _ _ _ hI a' ha' hpc'
    have htake := (Kernel.step_at_take ht1 hsys hat hnr hs).2
    obtain ⟨hes, rfl⟩ := step_takeS hN hT ht1 hI ha hpc hs
    subst hes
    have hsa : Kernel.siteAt abi μ th.st = some .take := by
      unfold Kernel.siteAt; rw [ite_eq_left_iff.mpr (fun h => absurd (by rw [ha, ← hpc]; rfl) h)]
    have hca := Kernel.certAfter_take ht1 htake hsa
      hsys (A64.deps_of_atNop (atNop_of_cellAt hcn)) (fun a _ => by rw [hk]; exact hz a) hcert0
    obtain ⟨c', fs', hlr, hI', htk'⟩ := hrun t.2.pmem
    have hj : j = 0 := by
      rcases hwr with h | ⟨h, -⟩
      · exact h
      · rw [hsys] at h; cases h
    subst hj
    obtain rfl : hl = [] := by
      rcases hh with ⟨h, -⟩ | ⟨-, h, -⟩
      · exact h
      · exact absurd h hntk
    have hk' : ({ t.2 with held := (0, rS) :: t.2.held, pmem := Kernel.eraseRange t.2.pmem rS } : Kernel.KState) =
        KS E Λ 0 [(0, rS)] (Kernel.eraseRange pm rS) := by rw [hk]; rfl
    obtain ⟨s', hrun', hpre'⟩ := pre_localJ (J := I) (u := { th with st := abi.skip (abi.setDmem th.st
        (Kernel.copyRange t.2.pmem (abi.dmem th.st) rS)) })
      (t' := (t.1.withThread 0 _ t.1.mem, _)) hP (withThread_one hth) hk'
      (fun a => by rw [Kernel.byte_eraseRange]; split <;> simp [hz])
      (.inr ⟨rfl, htk', hT.owned _ _ _ _ _ hI' htk'⟩) (hca _ (by erw [withThread_one hth]; rfl)) hs0 hσ
      hp hI' hw ⟨hb.1, hb.2⟩ ⟨hinv.1, hinv.2, hinv.3⟩ hown hmi hfi hgi
      (by show ExtRows.OwnOk (own (abi.skip _) fs') _ _
          rw [hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'), hN.ownTake _ _ _ _ _ hI a ha hpc]; exact hoo)
      (hN.noAlloc _ _ _ _ _ (IRun.of hI')) hfr ⟨tr, hreach⟩ hhi hcr
      (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hlr
    exact ⟨s', hrun', .inl hpre'⟩
  have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => htk ⟨a, ha, hpc⟩
  have hsite := no_siteS hN ht1 hI hnt
  have hready := atSys_of_ready (t := t) (th := th)
  have hsp := no_spawnS (t' := t') hN hT ht1 hI
  have hwj : t.2.wr 0 = j := wr_one hk
  have hwr' := wr_le hk hwr
  rcases A64Ext.step_cases_site ht1 hw hinv hs hsp hsite with
    ⟨rfl, hns, outs, o, hso, ho, rfl, hw', hc⟩ | ⟨rfl, w, rfl, hinv', hc, hwt⟩ | ⟨pk, hsys, hcert, hi⟩
  · -- an instruction: the row's frame run, then the row
    have hj : j = 0 := by
      rcases hwr with h | ⟨h, -⟩
      · exact h
      · rw [hns] at h; cases h
    subst hj
    have hth' := withThread_one (u := o.thread) (mem := o.mem) hth
    have hsn := siteAt_noneS hN hI hnt
    have hi := (stepOne_allInv Arch.armv8 hso ho (hT.instr _ _ _ _ _ hI hsn hns) ⟨fun _ => trivial, fun _ _ => trivial⟩).1
    have hb' := (stepOne_bnd _ hso ho hb).1
    have hfi' : MemFits o.mem := by
      refine ⟨fits_stepOne Arch.armv8 (fun _ he => certExec_fit hw ((Kernel.certExec_of_not_atSys abi hns).trans he))
        hso ho hfi.1, ?_⟩
      unfold InitFits; rw [(stepOne_dord _ hso ho).2.2.1.1]; exact hfi.2
    obtain ⟨c₁, fs₁, hr0, hown_eq, hout⟩ := hN.row hI hnt
    have hI1 : IRun p I lbl lsize th.st c₁ fs₁ := IRun.trans hI hr0
    have hoo₁ : ExtRows.OwnOk (own th.st fs₁) t.1.mem th.prom := by rw [hown_eq]; exact hoo
    have hsrc : (fs₁ = [] → ∀ a, c₁.term ≠ .ret a) →
        (SrcSem.source P p).Run s [] { s with ths := #[thAt th0 c₁ fs₁] } :=
      fun hr1 => frun_one hP hr0 hs0 rfl rfl hσ rfl hp hcr hr1
    have hmg : MemIn Λ o.mem ∧ MemInv G o.mem := by
      rcases ExtRows.out_mem hinv hso ho hns (A64Ext.wide8_exec hw hns) hgi hoo₁ hout with hm | ⟨L, V, hm, hL8L⟩
      · rw [hm]; exact ⟨hmi, hgi⟩
      · rw [hm]
        rcases hL8L with ⟨hL8, hL⟩
        have hLw := loc_eq_wordLoc hL8
        have h8 : Kernel.locBytes L = 8 := by simp [Kernel.locBytes, hL8]
        rcases hL with ⟨-, hmp, hGV⟩ | ⟨x, a, b, e, ty, w, sa, ht, hev, hv, hsa⟩ |
          ⟨x, sa, u, v, e, hxs, hA⟩ | ⟨-, -, ⟨xn, an, τn, en, hnb⟩, -⟩
        · exact ⟨memIn_append (hmp.2 rfl) hmi, hgi.append hGV⟩
        · obtain ⟨k, m, hkm, hml⟩ := hsafe.cell₁ (reach_run hreach (hsrc fun _ a' h => by rw [ht] at h; cases h))
            hI1 (.inr ⟨b, ht⟩) hev hsa
          obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
          rw [hml] at hoff
          rw [hsa] at hv
          have hwa := wordAddr_of_valRep_loc0 hv
          refine ⟨memIn_append (fun i hi => ?_) hmi, hgi.append ?_⟩
          · rw [h8] at hi
            exact shared_of_wordAddr hinv.mem hwa hoff i hi
          · show G L V
            rw [hLw]; exact hGpl _ V (heapData_of_wordAddr hinv.mem hwa hoff)
        · obtain ⟨k, m, hkm, hml⟩ := hsafe.xchg₁ (reach_run hreach (hsrc fun _ => xchgSite_not_ret hxs)) hI1 hxs
          obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
          rw [hml] at hoff
          have hwa := wordAddr_of_valRep_loc0 hA
          refine ⟨memIn_append (fun i hi => ?_) hmi, hgi.append ?_⟩
          · rw [h8] at hi
            exact shared_of_wordAddr hinv.mem hwa hoff i hi
          · show G L V
            rw [hLw]; exact hGpl _ V (heapData_of_wordAddr hinv.mem hwa hoff)
        · exact absurd hnb (hN.noAlloc _ _ _ _ _ hI1 xn an τn en)
    obtain ⟨hmi', hgi'⟩ := hmg
    have hoo' : ExtRows.OwnOk (own o.thread.st fs₁) o.mem o.thread.prom := by
      obtain ⟨tree, hex⟩ := Option.isSome_iff_exists.mp (ExtRows.out_exec hns hout)
      exact ownOk_step hex (hN.ownInstr _ _ _ _ _ hI1 hns tree hex) hinv.coh hinv.mem.tq_nodup
        (fun p hp => (hinv.mem.tq_le p hp).2) hso ho hoo₁
    rcases ExtRows.out_local hinv hso ho hns (A64Ext.wide8_exec hw hns) hgi hoo₁ hout with
      ⟨c', hr, hX, hinv'⟩ |
      ⟨kl, A, g, x, a, e, ty, w, sa, hex, ht, hev, hv, hsa, hX⟩ |
      ⟨kr, A, V, s', x, a, b, e, ty, tb, w, wb, sa, hex, ht, hev, hv, hsa, hevb, hvb, hX⟩ |
      ⟨kl, A, g, x, sa, u, v, e, hex, hxs, hA, hh0, hX⟩ |
      ⟨kr, A, V, s', x, sa, u, v, e, tv, wv, wold, hex, hxs, hA, hh0, hev, hvb, hX⟩ |
      ⟨x, a, τ, e, -, -, -, -, ht, -⟩ | ⟨-, -, x, a, τ, e, -, -, -, -, -, -, -, ht, -⟩
    · -- a local run: the row's run and the landing's pending run
      obtain ⟨s', hrun, hpre⟩ := pre_localJ (J := PendN p I) (t' := (t.1.withThread 0 o.thread o.mem, t.2)) hP hth'
        hk hz (hh.of_iff hi (hT.ownedN hX)) hc hs0 hσ hp hX hw' hb' hinv' (ownMsgs_step hso ho hown) hmi' hfi' hgi'
        hoo' hX.noAlloc hfr ⟨tr, hreach⟩ hhi hcr hX.noRet (hr0.trans (FrameRun.ofLocal hr fs₁))
      exact pend_land hP hN hrun hpre
    · -- the load row
      have hrun1 := hsrc fun _ a' h => by rw [ht] at h; cases h
      obtain ⟨jl, hjl⟩ := exists_sLatest (hsafe.cell₁ (reach_run hreach hrun1) hI1 (.inl ht) hev hsa)
      rw [hsa] at hv
      rw [← wordLoc_toNat] at hex
      obtain ⟨-, -, hinv', -⟩ := hinv.load hwf _ hex hso ho (wordAddr_of_valRep_loc0 hv) hjl
      obtain ⟨-, k, v, hgv, htl, hrd'⟩ := stepOne_load_tlatestP _ hex hso ho hinv.coh
      obtain ⟨m, hm, hrep⟩ := hinv.mem.latestP_read hwf hinv.narrow (wordAddr_of_valRep_loc0 hv)
        (SLatestP.nil_iff.mpr hjl) htl hrd'
      have hX' := hX v ⟨m.val, m.view, jl⟩ (hrd _) (valRep_setWidth_of_fits hrep (read?_fits hfi.1 hfi.2 hrd'))
      obtain ⟨th', hstep, hte, hen, hp', hσ', hst', hna'⟩ := src_load_stepS (p := p)
        (c := { s with ths := #[thAt th0 c₁ fs₁] }) (th := thAt th0 c₁ fs₁) hP rfl hp ht hev hsa
        (hN.cell _ _ _ _ _ hI1 x a e ty w (.inl ht) hev) hjl hm hX'.noRet
      have hrun := run_trans0 hrun1 (run_one hstep)
      refine pend_land hP hN hrun ⟨o.thread, th', 0, lbl, lsize, ts, hl, pm, none, hth', ⟨E, hk⟩, hz,
        hh.of_iff hi (hT.ownedN (by rw [hgv]; exact hX')), .inl rfl, hc, rfl, hσ'.trans hσ, hp', ?_, trivial,
        hw', hb', hinv', ownMsgs_step hso ho hown, hmi', hfi', hgi', ?_, heapCtr_of ?_,
        freshInv_one hs0 rfl rfl rfl hna' hfr, _, reach_run hreach hrun⟩
      · show PendN p I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩ th'.stack
        rw [hte, hen, hst', hgv]; exact hX'
      · show ExtRows.OwnOk (own o.thread.st th'.stack) _ _
        rw [hst']; exact hoo'
      · show ∀ x a τ e, th'.term ≠ _
        rw [hte]; exact hX'.noAlloc
    · -- the store row
      have hrun1 := hsrc fun _ a' h => by rw [ht] at h; cases h
      obtain ⟨k, m, hkm, hml⟩ := hsafe.cell₁ (reach_run hreach hrun1) hI1 (.inr ⟨b, ht⟩) hev hsa
      obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
      rw [hml] at hoff
      obtain ⟨th', mv, hstep, hte, hen, hp', hσ', hst', hna'⟩ := src_store_stepS (p := p)
        (c := { s with ths := #[thAt th0 c₁ fs₁] }) (th := thAt th0 c₁ fs₁) hP rfl hp ht hev hsa
        (hN.cell _ _ _ _ _ hI1 x a e ty w (.inr ⟨b, ht⟩) hev) hevb hX.noRet
      rw [hsa] at hv
      rw [← wordLoc_toNat] at hex
      obtain ⟨hst'', q, hinv'⟩ := hinv.store (m := ⟨sa, wb.val, mv⟩) _ hex hso ho (wordAddr_of_valRep_loc0 hv) hoff hvb
      have hrun := run_trans0 hrun1 (run_one hstep)
      refine pend_land hP hN hrun ⟨o.thread, th', 0, lbl, lsize, _, hl, pm, none, hth', ⟨E, hk⟩, hz,
        hh.of_iff hi (hT.ownedN (by rw [hst'']; exact hX)), .inl rfl, hc, rfl, hσ'.trans hσ, hp', ?_, trivial,
        hw', hb', hinv', ownMsgs_step hso ho hown, hmi', hfi', hgi', ?_, heapCtr_of ?_,
        freshInv_one hs0 rfl rfl rfl hna' hfr, _, reach_run hreach hrun⟩
      · show PendN p I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩ th'.stack
        rw [hte, hen, hst', hst'']; exact hX
      · show ExtRows.OwnOk (own o.thread.st th'.stack) _ _
        rw [hst']; exact hoo'
      · show ∀ x a τ e, th'.term ≠ _
        rw [hte]; exact hX.noAlloc
    · -- the load of an exchange: the source stutters after the row's run, holding the latest word
      have hrun1 := hsrc fun _ => xchgSite_not_ret hxs
      obtain ⟨k, m0, hkm, hml⟩ := hsafe.xchg₁ (reach_run hreach hrun1) hI1 hxs
      obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m0 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
      rw [hml] at hoff
      obtain ⟨jl, hjl⟩ := exists_sLatest ⟨k, m0, hkm, hml⟩
      have hwa := wordAddr_of_valRep_loc0 hA
      rw [← wordLoc_toNat] at hex
      obtain ⟨-, -, hinv', -⟩ := hinv.load hwf _ hex hso ho hwa hjl
      obtain ⟨-, k', r, hgr, htl, hrd'⟩ := stepOne_load_tlatestP _ hex hso ho hinv.coh
      obtain ⟨m, hm, hrep⟩ := hinv.mem.latestP_read hwf hinv.narrow hwa (SLatestP.nil_iff.mpr hjl) htl hrd'
      have hX' := hX r ⟨m.val, m.view, jl⟩ (hrd _) (valRep_setWidth_of_fits hrep (read?_fits hfi.1 hfi.2 hrd'))
      refine pend_land hP hN hrun1 ⟨o.thread, thAt th0 c₁ fs₁, 0, lbl, lsize, ts, hl, pm,
        some (A.toNat, ⟨m.val, m.view, jl⟩), hth', ⟨E, hk⟩, hz, hh.of_iff hi (hT.ownedN (by rw [hgr]; exact hX')),
        .inl rfl, hc, rfl, hσ, hp, ?_, ⟨sa, jl, m, hwa, hoff, hjl, hm, rfl⟩, hw', hb', hinv',
        ownMsgs_step hso ho hown, hmi', hfi', hgi', hoo', heapCtr_of hX'.noAlloc,
        freshInv_one hs0 rfl rfl rfl rfl hfr, _, reach_run hreach hrun1⟩
      rw [hgr]; exact hX'
    · -- the store of an exchange: the source exchange after the row's run, reading the held word
      have hrun1 := hsrc fun _ => xchgSite_not_ret hxs
      obtain ⟨k, m0, hkm, hml⟩ := hsafe.xchg₁ (reach_run hreach hrun1) hI1 hxs
      obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m0 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
      rw [hml] at hoff
      have hwa := wordAddr_of_valRep_loc0 hA
      have hhi1 : HoldInv lbl lsize s.mem c₁.hold := holdInv_frameRun hr0 hhi
      rw [hh0] at hhi1
      obtain ⟨sa', jl, m, hwa', hoff', hjl, hm, rfl⟩ := hhi1
      have hsa' : sa' = sa := hinv.mem.wordAddr_inj hwa' hwa hoff' hoff
      subst sa'
      obtain ⟨th', mv, hstep, hte, hen, hp', hσ', hst', hna'⟩ := src_swap_stepS (p := p)
        (c := { s with ths := #[thAt th0 c₁ fs₁] }) (th := thAt th0 c₁ fs₁) hP rfl hp hxs hev hjl hm
        (xchgSite_not_ret hxs) hX.noRet
      rw [← wordLoc_toNat] at hex
      obtain ⟨hst'', q, hinv'⟩ := hinv.store (m := ⟨sa, wv.val, mv⟩) _ hex hso ho hwa hoff hvb
      have hrun := run_trans0 hrun1 (run_one hstep)
      refine pend_land hP hN hrun ⟨o.thread, th', 0, lbl, lsize, _, hl, pm, none, hth', ⟨E, hk⟩, hz,
        hh.of_iff hi (hT.ownedN (by rw [hst'']; exact hX)), .inl rfl, hc, rfl, hσ'.trans hσ, hp', ?_, trivial,
        hw', hb', hinv', ownMsgs_step hso ho hown, hmi', hfi', hgi', ?_, heapCtr_of ?_,
        freshInv_one hs0 rfl rfl rfl hna' hfr, _, reach_run hreach hrun⟩
      · show PendN p I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩ th'.stack
        rw [hte, hen, hst', hst'']; exact hX
      · show ExtRows.OwnOk (own o.thread.st th'.stack) _ _
        rw [hst']; exact hoo'
      · show ∀ x a τ e, th'.term ≠ _
        rw [hte]; exact hX.noAlloc
    · exact absurd ht (hN.noAlloc _ _ _ _ _ hI1 x a τ e)
    · exact absurd ht (hN.noAlloc _ _ _ _ _ hI1 x a τ e)
  · -- a promise: the source stutters
    have hlast : t.1.mem.last ≤ (t.1.mem.append w).1.last := by rw [Memory.last_append]; exact Nat.le_succ _
    exact ⟨s, .refl _, .inl ⟨_, th0, j, lbl, lsize, ts, hl, pm, hd, withThread_one hth, ⟨E, hk⟩, hz, hh, hwr, hc, hs0,
      hσ, hp, hI, hhi, hw, ⟨hb.views.mono hlast, hb.regs.mono hlast⟩, hinv', ownMsgs_append hwt hown,
      memIn_append (hps t s th w hpre hth hwt hc).1 hmi,
      ⟨fits_promise_cert_on (soloFit64CodeOn μ t.2 0) (soloWideInv μ t.2 0) hw hc hfi.1, initFits_append hfi.2 w⟩,
      hgi.append (hps t s th w hpre hth hwt hc).2,
      ownOk_promise hinv.coh hinv.mem.tq_nodup (fun p hp => (hinv.mem.tq_le p hp).2) hoo w, hhc, hfr, tr, hreach⟩⟩
  · -- a kernel step
    obtain ⟨hr, call, hcall, hcases⟩ := Kernel.sysStep_cases (K := abi) ht1 hsys hwr'
    have hsys' := hready hr
    obtain ⟨call', hdc, hnx, -, hfd⟩ := hN.sysOk hT hI hsys'
    obtain rfl : call = call' := Option.some.inj (hcall.symm.trans hdc)
    rcases hcases with ⟨fd, buf, n, rd', b, u, rfl, rfl, hlt, hrb, hust, hes, rfl⟩ |
      ⟨r, rfl, hx, hg, hev, hmem, u, hu, hsu, hpu⟩ | ⟨hex, -⟩ | ⟨v, rfl, hx⟩
    · -- a byte of a `write` to `fd ≠ 1`: no event
      rw [ite_eq_right_iff.mpr (fun h => absurd h (hfd fd buf n rfl))] at hes
      subst hes
      refine ⟨s, .refl _, .inl ⟨u, th0, j + 1, lbl, lsize, ts, hl, pm, hd, withThread_one hth, ⟨E, by rw [hk]; rfl⟩, hz,
        hust ▸ hh, ?_, hcert u (by rw [withThread_one hth]; rfl), hs0, hσ, hp, hust ▸ hI, hhi, hust ▸ hw,
        ExtThread.bnd_readByte abi hb hrb, ExtThread.inv1_readByte abi hinv hrb, hown, hmi, hfi, hgi,
        by rw [hust, Kernel.readByte_prom hrb]; exact hoo, hhc, hfr, tr, hreach⟩⟩
      refine .inr ⟨hust ▸ hsys', fd, buf, n, ?_, hwj ▸ hlt⟩
      show Kernel.decode _ (abi.nr u.st) (abi.arg u.st) = _
      rw [hust]; exact hcall
    · -- a return: the row's frame run, then the local run to the successor
      obtain ⟨c₁, fs₁, call', hr0, hd', -, hx'⟩ := hN.sysRow hT hI hsys'
      obtain rfl : call = call' := Option.some.inj (hcall.symm.trans hd')
      obtain ⟨c', fs', hlr, hI'⟩ := hx' _ hsu
      have hbu : u.Bnd t'.1.mem.last := by
        rw [hmem]
        rcases ExtThread.bnd_sysStep abi ht1 hb hsys with he | ⟨u', he, hb'⟩
        · rw [he, hth] at hu; cases hu; exact hb
        · rw [he] at hu
          obtain rfl : u' = u := Option.some.inj ((show (t.1.withThread 0 u' t.1.mem).threads[0]? = some u' by
            simp only [Config.withThread, hth]; rfl).symm.trans hu)
          exact hb'
      have hu1 : t'.1.threads = #[u] ∧ Inv1 Λ lbl lsize ts u t'.1.mem s.mem := by
        rcases hi with he | ⟨u', he, hinv'⟩
        · rw [he] at hu ⊢; rw [hth] at hu; cases hu; exact ⟨hth, hinv⟩
        · rw [he] at hu ⊢
          have h1 : (t.1.withThread 0 u' t.1.mem).threads = #[u'] := withThread_one hth
          obtain rfl : u' = u := Option.some.inj ((show (t.1.withThread 0 u' t.1.mem).threads[0]? = some u' by
            simp only [Config.withThread, hth]; rfl).symm.trans hu)
          exact ⟨h1, hinv'⟩
      have hk' : t'.2 = KS E Λ 0 hl pm := by
        rcases ExtThread.sysStep_ret_kstate abi ht1 hsys (fun h => hx (Option.some.inj
          (hcall.symm.trans h))) (fun v h => hg v (Option.some.inj (hcall.symm.trans h))) with he | ⟨he, hw0⟩
        · rw [he, hk]; rfl
        · rw [he, hk]
          rcases hwr with rfl | ⟨-, fd, buf, n, hc', -⟩
          · rfl
          · have := hw0 fd buf n hc'; rw [hwj] at this; subst this; rfl
      have hobs : obs es = [] := by
        rcases hev with rfl | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
      rw [hobs]
      have hsu' : u.st ∈ Kernel.certSuccs abi th.st call := hsu
      obtain ⟨s', hrun, hpre⟩ := pre_localJ (J := I) (own := own) hP hu1.1 hk' hz
        (hh.of_iff (hT.sys _ _ _ _ _ hI hsys' _ hcall _ hsu') (hT.owned _ _ _ _ _ hI')) (hcert u hu) hs0 hσ hp hI'
        (ExtThread.sysStep_wideInv abi wideInv ht1 hw hsys hwr' hu) hbu hu1.2 (by rw [hmem]; exact hown)
        (by rw [hmem]; exact hmi) (by rw [hmem]; exact hfi) (by rw [hmem]; exact hgi)
        (by rw [hmem, hpu, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'),
              hN.ownSys _ _ _ _ _ (IRun.trans hI hr0) hsys' _ hcall _ hsu', hN.ownRun _ _ _ _ _ _ _ hr0 (.inl hI)]
            exact hoo)
        (hN.noAlloc _ _ _ _ _ (IRun.of hI')) hfr ⟨tr, hreach⟩ hhi hcr
        (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') (hr0.trans hlr)
      exact ⟨s', hrun, .inl hpre⟩
    · exact absurd hex hnx
    · rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨k, rfl, -, rfl, rfl⟩
      · -- `exit_group`: `main`'s exit at depth 0 (off every abort site, `Step.sys`)
        have hoff : ∀ k a, μ.abortAt k = some a → pcOf th.st ≠ a := fun k a ha hpc =>
          exit_off hs (List.mem_singleton_self _) k a ha ⟨th, ht1, hpc⟩
        obtain ⟨c₁, fs₁, call', hr0, hd', ⟨-, -, -, hex⟩, -⟩ := hN.sysRow hT hI hsys'
        obtain rfl : Kernel.Call.exitGroup v = call' := Option.some.inj (hcall.symm.trans hd')
        obtain ⟨c', hlr, ⟨hfs, hpl⟩, hexit⟩ := hex v rfl (fun ⟨k, a, ha, hpc⟩ => hoff k a ha hpc)
        subst hfs
        have hrun : (SrcSem.source P p).Run s
            (mainExit { s with ths := s.ths.set! 0 { th0 with term := c'.term, env := c'.env, stack := [] } })
            { s with ths := s.ths.set! 0 { th0 with term := c'.term, env := c'.env, stack := [] } } :=
          (hr0.trans (FrameRun.ofLocal hlr [])).run_source hP h0 rfl rfl hσ rfl hp hcr
            (hP.noExit hreach)
        have hlt : 0 < s.ths.size := by rw [hs0]; exact Nat.zero_lt_one
        rw [hexit _ { th0 with term := c'.term, env := c'.env, stack := [] } (by simp [hlt]) rfl rfl rfl] at hrun
        refine ⟨_, hrun, .inr ⟨th, { th0 with term := c'.term, env := c'.env, stack := [] }, j, lbl, lsize, ts, hl, pm,
          _, hth, ⟨E, by rw [hk]⟩, hz, hh, set_one hs0, hσ, hp, PlacedS.ofNil hpl, hinv, hown, hmi, _,
          reach_run hreach hrun⟩⟩
      · -- an abort: the process ends, the source stutters
        exact ⟨s, .refl _, .inr ⟨th, th0, j, lbl, lsize, ts, hl, pm, _, hth, ⟨E, by rw [hk]⟩, hz, hh, hs0, hσ, hp,
          by have hpl := hN.place _ _ _ _ _ hI; exact hpl, hinv, hown, hmi, tr, hreach⟩⟩

/-- **Every step from `RS` is matched** (`r_step` with the frames): from
`PreS` by `pre_stepS`; after the exit no thread steps. -/
theorem r_stepS (hP : HookOK P p) (hN : NodesS Λ p μ rd G own I) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hps : PromSharedS Λ P p G own I rS Tk μ cells ctr) (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev} (h : RS Λ P p G own I rS Tk μ cells ctr t s)
    (hs : T.M.Step μ tid t es t') :
    ∃ s', (SrcSem.source P p).Run s (obs es) s' ∧ RS Λ P p G own I rS Tk μ cells ctr t' s' := by
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩
  · exact pre_stepS hP hN hsafe hT hps hrd hwf hGpl h hs
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hk]) hs).elim

/-! ## The certification core -/

/-- **The core of `PreJ`** for a thread `th` and a memory `mem` (`PreCore`
with the frames), over a fragment `J`: kept along the thread's
certification runs, the shared-region and `G` clauses on messages
exempting the outstanding promises (`MsgsExcept`). -/
def PreCoreJ (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (J : InvS)
    (th : Thread isaLSE2) (mem : Memory) (s : TermRun.Cfg) : Prop :=
  ∃ (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat) (hd : Option (Nat × TermRun.Word)),
    s.ths = #[th0] ∧ th0.σs = [] ∧ th0.promises = [] ∧
    J lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack ∧ HoldInv lbl lsize s.mem hd ∧ WideSt th.st ∧
    th.Bnd mem.last ∧ Inv1 Λ lbl lsize ts th mem s.mem ∧ OwnMsgs mem ∧
    MsgsExcept (fun m => LocIn Λ.shared m.loc) th.prom mem ∧ (∀ q ∈ mem.init, InitIn Λ q.1) ∧ MemFits mem ∧
    MsgsExcept (fun m => G m.loc m.val) th.prom mem ∧ (∀ l, G l (mem.initVal l)) ∧
    ExtRows.OwnOk (own th.st th0.stack) mem th.prom ∧ ∃ tr, (SrcSem.source P p).Reach tr s

/-- `PreCoreJ`'s message clauses, as `stepG_of` takes them. -/
theorem PreCoreJ.msgs {J : InvS} {th : Thread isaLSE2} {mem : Memory} {s : TermRun.Cfg}
    (h : PreCoreJ Λ P p G own J th mem s) :
    MsgsExcept (fun m => LocIn Λ.shared m.loc) th.prom mem ∧ MsgsExcept (fun m => G m.loc m.val) th.prom mem := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hsh, -, -, hgm, -⟩ := h
  exact ⟨hsh, hgm⟩

/-- **`PreJ` gives `PreCoreJ`** of its one thread and the memory. -/
theorem pre_coreS {J : InvS} {rS : Range} {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isaLSE2}
    (h : PreJ Λ P p G own J rS Tk μ cells ctr t s) (hth : t.1.threads = #[th]) :
    PreCoreJ Λ P p G own J th t.1.mem s := by
  obtain ⟨th', th0, -, lbl, lsize, ts, -, -, hd, hth', -, -, -, -, -, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown,
    hmi, hfi, hgi, hoo, -, -, hre⟩ := h
  obtain rfl : th = th' := (get_one hth (show t.1.threads[0]? = some th' by rw [hth']; rfl)).2
  exact ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, MsgsExcept.of_all hmi.1 _, hmi.2,
    hfi, MemInv.msgsExcept hgi _, hgi.1, hoo, hre⟩

/-- **`PreS` followed by a certified promise gives `PreCoreJ`** of the
promising thread and the memory with the promise (`pre_core_promise`). -/
theorem pre_core_promiseS {rS : Range} {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isaLSE2}
    {w : Msg} (h : PreS Λ P p G own I rS Tk μ cells ctr t s) (hth : t.1.threads = #[th]) (hwt : w.tid = 0)
    (hc : CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ t.2 0) 0 (Live.Sem.promThread th t.1.mem w)
      (t.1.mem.append w).1) :
    PreCoreJ Λ P p G own I (Live.Sem.promThread th t.1.mem w) (t.1.mem.append w).1 s := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hre⟩ := pre_coreS h hth
  have hlast : t.1.mem.last ≤ (t.1.mem.append w).1.last := by rw [Memory.last_append]; exact Nat.le_succ _
  exact ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, ⟨hb.views.mono hlast, hb.regs.mono hlast⟩,
    hinv.promise_cert_on (soloWide8CodeOn μ t.2 0) (soloWideInv μ t.2 0) hw hc, ownMsgs_append hwt hown,
    msgsExcept_promise hsh w, hini,
    ⟨fits_promise_cert_on (soloFit64CodeOn μ t.2 0) (soloWideInv μ t.2 0) hw hc hfi.1, initFits_append hfi.2 w⟩,
    msgsExcept_promise hgm w,
    hgi, ownOk_promise hinv.coh hinv.mem.tq_nodup (fun p hp => (hinv.mem.tq_le p hp).2) hoo w, hre⟩

/-- **A landing over `PendN` in the core**: the pending frame run taken
(`pend_run` without the kernel state). -/
theorem core_land (hP : HookOK P p) (hN : NodesS Λ p μ rd G own I) {th : Thread isaLSE2}
    {mem : Memory} {s s₂ : TermRun.Cfg} (hrun : (SrcSem.source P p).Run s [] s₂)
    (h : PreCoreJ Λ P p G own (PendN p I) th mem s₂) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJ Λ P p G own I th mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, ⟨hnr, -, c₂, fs₂, hr, hI⟩, hhi, hw, hb, hinv, hown, hsh, hini,
    hfi, hgm, hgi, hoo, tr, hreach⟩ := h
  have hrun' := frun_one (q := (⟨th0.term, th0.env, hd⟩, th0.stack)) hP hr hs0 rfl rfl hσ rfl hp hnr
    (fun h0 => hN.noRet _ _ _ _ (by simp only at h0; subst h0; exact hI))
  refine ⟨_, run_trans0 hrun hrun', thAt th0 c₂ fs₂, lbl, lsize, ts, c₂.hold, rfl, hσ, hp, hI,
    holdInv_frameRun hr hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, ?_, _, reach_run hreach hrun'⟩
  show ExtRows.OwnOk (own th.st fs₂) _ _
  rw [hN.ownRun _ _ _ _ _ _ _ hr (.inr hI)]; exact hoo

/-- **An instruction step off a system call and off the take site keeps
`PreCoreJ`** (`core_step` with the frames), matched by a source run with no
event: the row's frame run, the row, and its landing's pending run. -/
theorem core_stepS (hP : HookOK P p) (hN : NodesS Λ p μ rd G own I) (hsafe : SrcSafeS P p I)
    (hrd : ∀ w, rd w) (hwf : Λ.WF) (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {th : Thread isaLSE2} {mem : Memory} {s : TermRun.Cfg} {outs : List (Except String (Outcome isaLSE2))}
    {o : Outcome isaLSE2} (h : PreCoreJ Λ P p G own I th mem s) (hns : abi.atSys th.st = false)
    (hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a)
    (hso : stepOne Arch.armv8 th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJ Λ P p G own I o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    tr, hreach⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  obtain ⟨c₁, fs₁, hr0, hown_eq, hout⟩ := hN.row hI hnt
  have hI1 : IRun p I lbl lsize th.st c₁ fs₁ := IRun.trans hI hr0
  have hoo₁ : ExtRows.OwnOk (own th.st fs₁) mem th.prom := by rw [hown_eq]; exact hoo
  have hsrc : (fs₁ = [] → ∀ a, c₁.term ≠ .ret a) →
      (SrcSem.source P p).Run s [] { s with ths := #[thAt th0 c₁ fs₁] } :=
    fun hr1 => frun_one hP hr0 hs0 rfl rfl hσ rfl hp hcr hr1
  obtain ⟨tree, hex⟩ := Option.isSome_iff_exists.mp (ExtRows.out_exec hns hout)
  have hw' : WideSt o.thread.st :=
    wideInv _ _ _ hw ((Kernel.certExec_of_not_atSys abi hns).trans hex) (ExtThread.stepOne_treeLeaf hex hso ho)
  have hb' := (stepOne_bnd _ hso ho hb).1
  have hinit : o.mem.init = mem.init := (stepOne_dord _ hso ho).2.2.1.1
  have hfi' : MemFits o.mem := by
    refine ⟨fits_stepOne Arch.armv8 (fun _ he => certExec_fit hw ((Kernel.certExec_of_not_atSys abi hns).trans he))
      hso ho hfi.1, ?_⟩
    unfold InitFits; rw [hinit]; exact hfi.2
  have hini' : ∀ q ∈ o.mem.init, InitIn Λ q.1 := by rw [hinit]; exact hini
  have hgi' : ∀ l, G l (o.mem.initVal l) := by intro l; unfold Memory.initVal; rw [hinit]; exact hgi l
  have hoo' : ExtRows.OwnOk (own o.thread.st fs₁) o.mem o.thread.prom :=
    ownOk_step hex (hN.ownInstr _ _ _ _ _ hI1 hns tree hex) hinv.coh hinv.mem.tq_nodup
      (fun p hp => (hinv.mem.tq_le p hp).2) hso ho hoo₁
  have hown' := ownMsgs_step hso ho hown
  have hmg : MsgsExcept (fun m => LocIn Λ.shared m.loc) o.thread.prom o.mem ∧
      MsgsExcept (fun m => G m.loc m.val) o.thread.prom o.mem := by
    rcases ExtRows.out_memP hinv hso ho hns (A64Ext.wide8_exec hw hns) hgm hgi hoo₁ hout with
      ⟨hm, hpr⟩ | ⟨L, V, hL8, hmem, hL⟩
    · exact ⟨msgsExcept_of_eq hsh hm hpr, msgsExcept_of_eq hgm hm hpr⟩
    have hLw := loc_eq_wordLoc hL8
    have h8 : Kernel.locBytes L = 8 := by simp [Kernel.locBytes, hL8]
    have hPm : LocIn Λ.shared L ∧ G L V := by
      rcases hL with ⟨-, hmp, hGV⟩ | ⟨x, a, b, e, ty, w, sa, ht, hev, hv, hsa⟩ |
        ⟨x, sa, u, v, e, hxs, hA⟩ | ⟨-, -, ⟨xn, an, τn, en, hnb⟩, -⟩
      · exact ⟨hmp.2 rfl, hGV⟩
      · obtain ⟨k, m, hkm, hl⟩ := hsafe.cell₁ (reach_run hreach (hsrc fun _ a' h => by rw [ht] at h; cases h))
          hI1 (.inr ⟨b, ht⟩) hev hsa
        obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
        rw [hl] at hoff
        rw [hsa] at hv
        have hwa := wordAddr_of_valRep_loc0 hv
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [h8] at hi
          exact shared_of_wordAddr hinv.mem hwa hoff i hi
        · rw [hLw]; exact hGpl _ V (heapData_of_wordAddr hinv.mem hwa hoff)
      · obtain ⟨k, m, hkm, hl⟩ := hsafe.xchg₁ (reach_run hreach (hsrc fun _ => xchgSite_not_ret hxs)) hI1 hxs
        obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
        rw [hl] at hoff
        have hwa := wordAddr_of_valRep_loc0 hA
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [h8] at hi
          exact shared_of_wordAddr hinv.mem hwa hoff i hi
        · rw [hLw]; exact hGpl _ V (heapData_of_wordAddr hinv.mem hwa hoff)
      · exact absurd hnb (hN.noAlloc _ _ _ _ _ hI1 xn an τn en)
    rcases hmem with ⟨hm, hpr⟩ | ⟨q, -, hg, hm, hpr⟩
    · rw [hm, hpr]
      exact ⟨msgsExcept_append hsh (w := ⟨L, V, 0⟩) hPm.1, msgsExcept_append hgm (w := ⟨L, V, 0⟩) hPm.2⟩
    · rw [hm, hpr]
      exact ⟨msgsExcept_erase hsh hg hPm.1, msgsExcept_erase hgm hg hPm.2⟩
  rcases ExtRows.out_localP hinv hso ho hns (A64Ext.wide8_exec hw hns) hgm hgi hoo₁ hout with
    ⟨c', hr, hX, hinv'⟩ |
    ⟨kl, A, g, x, a, e, ty, w, sa, hex, ht, hev, hv, hsa, hX⟩ |
    ⟨kr, A, V, s', x, a, b, e, ty, tb, w, wb, sa, hex, ht, hev, hv, hsa, hevb, hvb, hX⟩ |
    ⟨kl, A, g, x, sa, u, v, e, hex, hxs, hA, hh0, hX⟩ |
    ⟨kr, A, V, s', x, sa, u, v, e, tv, wv, wold, hex, hxs, hA, hh0, hev, hvb, hX⟩ |
    ⟨x, a, τ, e, -, -, -, -, ht, -⟩ | ⟨-, -, x, a, τ, e, -, -, -, -, -, -, -, ht, -⟩
  · -- a local run: the row's run and the landing's pending run
    have hr1 := hr0.trans (FrameRun.ofLocal hr fs₁)
    have hrun := frun_one hP hr1 hs0 rfl rfl hσ rfl hp hcr hX.noRet
    exact core_land hP hN hrun ⟨thAt th0 c' fs₁, lbl, lsize, ts, c'.hold, rfl, hσ, hp, hX,
      holdInv_frameRun hr1 hhi, hw', hb', hinv', hown', hmg.1, hini', hfi', hmg.2, hgi', hoo', _,
      reach_run hreach hrun⟩
  · -- the load row
    have hrun1 := hsrc fun _ a' h => by rw [ht] at h; cases h
    obtain ⟨jl, hjl⟩ := exists_sLatest (hsafe.cell₁ (reach_run hreach hrun1) hI1 (.inl ht) hev hsa)
    rw [hsa] at hv
    rw [← wordLoc_toNat] at hex
    obtain ⟨-, -, hinv', -⟩ := hinv.load hwf _ hex hso ho (wordAddr_of_valRep_loc0 hv) hjl
    obtain ⟨-, k, v, hgv, htl, hrd'⟩ := stepOne_load_tlatestP _ hex hso ho hinv.coh
    obtain ⟨m, hm, hrep⟩ := hinv.mem.latestP_read hwf hinv.narrow (wordAddr_of_valRep_loc0 hv)
      (SLatestP.nil_iff.mpr hjl) htl hrd'
    have hX' := hX v ⟨m.val, m.view, jl⟩ (hrd _) (valRep_setWidth_of_fits hrep (read?_fits hfi.1 hfi.2 hrd'))
    obtain ⟨th', hstep, hte, hen, hp', hσ', hst', -⟩ := src_load_stepS (p := p)
      (c := { s with ths := #[thAt th0 c₁ fs₁] }) (th := thAt th0 c₁ fs₁) hP rfl hp ht hev hsa
      (hN.cell _ _ _ _ _ hI1 x a e ty w (.inl ht) hev) hjl hm hX'.noRet
    have hrun := run_trans0 hrun1 (run_one hstep)
    refine core_land hP hN hrun ⟨th', lbl, lsize, ts, none, rfl, hσ'.trans hσ, hp', ?_, trivial, hw', hb', hinv',
      hown', hmg.1, hini', hfi', hmg.2, hgi', ?_, _, reach_run hreach hrun⟩
    · show PendN p I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩ th'.stack
      rw [hte, hen, hst', hgv]; exact hX'
    · show ExtRows.OwnOk (own o.thread.st th'.stack) _ _
      rw [hst']; exact hoo'
  · -- the store row
    have hrun1 := hsrc fun _ a' h => by rw [ht] at h; cases h
    obtain ⟨k, m, hkm, hml⟩ := hsafe.cell₁ (reach_run hreach hrun1) hI1 (.inr ⟨b, ht⟩) hev hsa
    obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
    rw [hml] at hoff
    obtain ⟨th', mv, hstep, hte, hen, hp', hσ', hst', -⟩ := src_store_stepS (p := p)
      (c := { s with ths := #[thAt th0 c₁ fs₁] }) (th := thAt th0 c₁ fs₁) hP rfl hp ht hev hsa
      (hN.cell _ _ _ _ _ hI1 x a e ty w (.inr ⟨b, ht⟩) hev) hevb hX.noRet
    rw [hsa] at hv
    rw [← wordLoc_toNat] at hex
    obtain ⟨hst'', q, hinv'⟩ := hinv.store (m := ⟨sa, wb.val, mv⟩) _ hex hso ho (wordAddr_of_valRep_loc0 hv) hoff hvb
    have hrun := run_trans0 hrun1 (run_one hstep)
    refine core_land hP hN hrun ⟨th', lbl, lsize, _, none, rfl, hσ'.trans hσ, hp', ?_, trivial, hw', hb', hinv',
      hown', hmg.1, hini', hfi', hmg.2, hgi', ?_, _, reach_run hreach hrun⟩
    · show PendN p I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩ th'.stack
      rw [hte, hen, hst', hst'']; exact hX
    · show ExtRows.OwnOk (own o.thread.st th'.stack) _ _
      rw [hst']; exact hoo'
  · -- the load of an exchange: the source stutters after the row's run, holding the latest word
    have hrun1 := hsrc fun _ => xchgSite_not_ret hxs
    obtain ⟨k, m0, hkm, hml⟩ := hsafe.xchg₁ (reach_run hreach hrun1) hI1 hxs
    obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m0 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
    rw [hml] at hoff
    obtain ⟨jl, hjl⟩ := exists_sLatest ⟨k, m0, hkm, hml⟩
    have hwa := wordAddr_of_valRep_loc0 hA
    rw [← wordLoc_toNat] at hex
    obtain ⟨-, -, hinv', -⟩ := hinv.load hwf _ hex hso ho hwa hjl
    obtain ⟨-, k', r, hgr, htl, hrd'⟩ := stepOne_load_tlatestP _ hex hso ho hinv.coh
    obtain ⟨m, hm, hrep⟩ := hinv.mem.latestP_read hwf hinv.narrow hwa (SLatestP.nil_iff.mpr hjl) htl hrd'
    have hX' := hX r ⟨m.val, m.view, jl⟩ (hrd _) (valRep_setWidth_of_fits hrep (read?_fits hfi.1 hfi.2 hrd'))
    refine core_land hP hN hrun1 ⟨thAt th0 c₁ fs₁, lbl, lsize, ts, some (A.toNat, ⟨m.val, m.view, jl⟩), rfl, hσ,
      hp, ?_, ⟨sa, jl, m, hwa, hoff, hjl, hm, rfl⟩, hw', hb', hinv', hown', hmg.1, hini', hfi', hmg.2, hgi', hoo',
      _, reach_run hreach hrun1⟩
    rw [hgr]; exact hX'
  · -- the store of an exchange: the source exchange after the row's run, reading the held word
    have hrun1 := hsrc fun _ => xchgSite_not_ret hxs
    obtain ⟨k, m0, hkm, hml⟩ := hsafe.xchg₁ (reach_run hreach hrun1) hI1 hxs
    obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m0 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
    rw [hml] at hoff
    have hwa := wordAddr_of_valRep_loc0 hA
    have hhi1 : HoldInv lbl lsize s.mem c₁.hold := holdInv_frameRun hr0 hhi
    rw [hh0] at hhi1
    obtain ⟨sa', jl, m, hwa', hoff', hjl, hm, rfl⟩ := hhi1
    have hsa' : sa' = sa := hinv.mem.wordAddr_inj hwa' hwa hoff' hoff
    subst sa'
    obtain ⟨th', mv, hstep, hte, hen, hp', hσ', hst', -⟩ := src_swap_stepS (p := p)
      (c := { s with ths := #[thAt th0 c₁ fs₁] }) (th := thAt th0 c₁ fs₁) hP rfl hp hxs hev hjl hm
      (xchgSite_not_ret hxs) hX.noRet
    rw [← wordLoc_toNat] at hex
    obtain ⟨hst'', q, hinv'⟩ := hinv.store (m := ⟨sa, wv.val, mv⟩) _ hex hso ho hwa hoff hvb
    have hrun := run_trans0 hrun1 (run_one hstep)
    refine core_land hP hN hrun ⟨th', lbl, lsize, _, none, rfl, hσ'.trans hσ, hp', ?_, trivial, hw', hb', hinv',
      hown', hmg.1, hini', hfi', hmg.2, hgi', ?_, _, reach_run hreach hrun⟩
    · show PendN p I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩ th'.stack
      rw [hte, hen, hst', hst'']; exact hX
    · show ExtRows.OwnOk (own o.thread.st th'.stack) _ _
      rw [hst']; exact hoo'
  · exact absurd ht (hN.noAlloc _ _ _ _ _ hI1 x a τ e)
  · exact absurd ht (hN.noAlloc _ _ _ _ _ hI1 x a τ e)

/-- **A certification step at a system call keeps `PreCoreJ`** (`core_sys`
with the frames): the row's frame run, then the local run to the
successor. -/
theorem core_sysS (hP : HookOK P p) (hN : NodesS Λ p μ rd G own I) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {th : Thread isaLSE2} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2} {x : Kernel.KState}
    (h : PreCoreJ Λ P p G own I th mem s) (hsi : Kernel.siteAt abi μ th.st = none) (hs : abi.atSys th.st = true)
    (hso : (Kernel.certSem abi Arch.armv8 μ x 0).step Arch.armv8 th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJ Λ P p G own I o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    tr, hreach⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  obtain ⟨c₁, fs₁, call, hr0, hdc, ⟨-, hcl, -, -⟩, hx⟩ := hN.sysRow hT hI hs
  obtain ⟨hm, hpr, hsu, hinv'⟩ := hinv.certSysSolo hsi hs hdc hcl hso ho
  obtain ⟨c', fs', hlr, hI'⟩ := hx _ hsu
  have hr1 := hr0.trans hlr
  have hrun := frun_one hP hr1 hs0 rfl rfl hσ rfl hp hcr (fun h0' => by
    have h0'' : fs' = [] := h0'
    subst h0''; exact hN.noRet _ _ _ _ hI')
  have hw' : WideSt o.thread.st := wideSt_soloLeaf hw (Kernel.certSuccs_soloLeaf hsu)
  refine ⟨_, hrun, thAt th0 c' fs', lbl, lsize, ts, c'.hold, rfl, hσ, hp, hI', holdInv_frameRun hr1 hhi, hw',
    (stepOneWith_bnd _ hso ho hb).1, hinv', ?_, ?_, ?_, ?_, ?_, ?_, ?_, _, reach_run hreach hrun⟩
  · rw [hm]; exact hown
  · rw [hm, hpr]; exact hsh
  · rw [hm]; exact hini
  · rw [hm]; exact hfi
  · rw [hm, hpr]; exact hgm
  · rw [hm]; exact hgi
  · show ExtRows.OwnOk (own o.thread.st fs') _ _
    rw [hm, hpr, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'), hN.ownSys _ _ _ _ _ (IRun.trans hI hr0) hs _ hdc _ hsu,
      hN.ownRun _ _ _ _ _ _ _ hr0 (.inl hI)]
    exact hoo

/-- **The certification step at a transfer site keeps `PreCoreJ`**
(`core_site` with the frames; the take's local run keeps them). -/
theorem core_siteS (hP : HookOK P p) (hN : NodesS Λ p μ rd G own I) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {th : Thread isaLSE2} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2} {x : Kernel.KState}
    (h : PreCoreJ Λ P p G own I th mem s) (hsi : Kernel.siteAt abi μ th.st ≠ none)
    (hso : (Kernel.certSem abi Arch.armv8 μ x 0).step Arch.armv8 th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJ Λ P p G own I o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    tr, hreach⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  have ha : μ.site .take = some (pcOf th.st) := Classical.byContradiction fun hne =>
    hsi (Kernel.siteAt_eq_none_iff.mpr ⟨fun h => hne h, fun h => hN.noSite _ _ _ _ _ hI _ h rfl⟩)
  have hsa : Kernel.siteAt abi μ th.st = some .take := by
    unfold Kernel.siteAt; exact ite_eq_left ha
  obtain ⟨-, ⟨sz, hcn⟩, hsys, hsr, -, -, -, hrun⟩ := hT.site _ _ _ _ _ hI _ ha rfl
  obtain ⟨hot, hom⟩ := Kernel.certSem_step_take_out hsa hsys (A64.deps_of_atNop (atNop_of_cellAt hcn)) hso ho
  rw [hsr] at hot
  rw [hot, hom]
  obtain ⟨c', fs', hr1, hI', -⟩ := hrun x.pmem
  have hrun' := frun_one hP hr1 hs0 rfl rfl hσ rfl hp hcr (fun h0' => by
    have h0'' : fs' = [] := h0'
    rw [h0''] at hI'; exact hN.noRet _ _ _ _ hI')
  exact ⟨_, hrun', thAt th0 c' fs', lbl, lsize, ts, c'.hold, rfl, hσ, hp, hI', holdInv_frameRun hr1 hhi, hw,
    ⟨hb.1, hb.2⟩, ⟨hinv.1, hinv.2, hinv.3⟩, hown, hsh, hini, hfi, hgm, hgi,
    by show ExtRows.OwnOk (own (abi.skip _) fs') _ _
       rw [hN.ownRun _ _ _ _ _ _ _ hr1 (.inr hI'), hN.ownTake _ _ _ _ _ hI _ ha rfl]; exact hoo, _,
    reach_run hreach hrun'⟩

/-- **Every instruction step off a system call and off the transfer sites
keeps `PreCoreJ`** (the form of `stepG_of`'s `hins`), by `core_stepS`. -/
theorem core_insS (hP : HookOK P p) (hN : NodesS Λ p μ rd G own I) (hsafe : SrcSafeS P p I)
    (hrd : ∀ w, rd w) (hwf : Λ.WF) (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) :
    ∀ th mem s outs o, PreCoreJ Λ P p G own I th mem s → Kernel.siteAt abi μ th.st = none →
      abi.atSys th.st = false → stepOne Arch.armv8 th 0 mem = some outs → .ok o ∈ outs →
      ∃ s', PreCoreJ Λ P p G own I o.thread o.mem s' := by
  intro th mem s outs o h hsi hns hso ho
  have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc =>
    (Kernel.siteAt_eq_none_iff.mp hsi).1 (by rw [ha, ← hpc]; rfl)
  obtain ⟨s', -, h'⟩ := core_stepS hP hN hsafe hrd hwf hGpl h hns hnt hso ho
  exact ⟨s', h'⟩

/-- **`PromSharedS` from the node obligations** (`promShared_a64` with the
frames): `PreCoreJ` is the certification run's invariant
(`A64PromShared.stepG_of`), and a certified promise from `PreS` lands in it
(`pre_core_promiseS`). -/
theorem promSharedS (hP : HookOK P p) (hN : NodesS Λ p μ rd G own I) (hsafe : SrcSafeS P p I)
    (hrd : ∀ w, rd w) (hwf : Λ.WF) (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) :
    PromSharedS Λ P p G own I rS Tk μ cells ctr := by
  intro t s th w hpre hth hw hc
  exact certOkC_prom_good_cfg
    (A64PromShared.stepG_of (Core := PreCoreJ Λ P p G own I) (fun _ _ _ h => h.msgs)
      (core_insS hP hN hsafe hrd hwf hGpl)
      (fun _ _ _ _ _ _ h hsi hs hso ho => (core_sysS hP hN hT h hsi hs hso ho).imp fun _ h => h.2)
      (fun _ _ _ _ _ _ h hsi hso ho => (core_siteS hP hN hT h hsi hso ho).imp fun _ h => h.2) t.2)
    ⟨s, pre_core_promiseS hpre hth hw hc⟩ hc
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (Memory.get?_append_new (m := t.1.mem))

/-! ## The load -/

open Scc.Cert.Link in
/-- **The start is related** (`pre_load` with the frames): the loaded
thread at the start pair at no frames, thread 0's labels from 0 on unplaced
under the static placement (`hfr0`; at `main`'s start no buffer is
allocated, so `HeapCtr` holds vacuously). -/
theorem pre_loadS {Λ : Scc.Sem.Layout} {G : Loc → Val → Prop} {own : OwnS} {I : InvS} {μ : Marks}
    {prog : Program} {syms : List (String × Nat)} {mem : List (Loc × Val)} {lsize : Lsize} {secs : DataSecs}
    {code : String → Option Nat} {name : WeakMem.AllocLabel → String}
    (himg : imageOk Λ secs code = true) (hss : StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hinit : P.init (s0 P.cap)) (hst : I Λ.static lsize (threadAt E Λ.code.lo prog syms) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (hmem : ∀ q ∈ mem, InitIn Λ q.1) (hmf : ∀ q ∈ mem, q.2.toNat < 2 ^ 64) {rS : Range} {Tk : State → Prop}
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog syms))
    (hown0 : OwnInit (own (threadAt E Λ.code.lo prog syms) [])
      (loadProg (kernel 1) E Λ prog syms mem).1.mem)
    (hg : MemInv G (loadProg (kernel 1) E Λ prog syms mem).1.mem) :
    PreS Λ P p G own I rS Tk μ cells ctr (loadProg (kernel 1) E Λ prog syms mem) (s0 P.cap) := by
  refine ⟨Thread.init (threadAt E Λ.code.lo prog syms), _, 0, Λ.static, lsize, fun _ => none, [], ∅, none,
    rfl, ?_, fun _ => by simp [Kernel.byte],
    .inl ⟨rfl, htk0⟩, .inl rfl, certOkC_of_prom_nil rfl, rfl, rfl, rfl, hst, trivial,
    wideSt_threadAt hw _ _ _,
    bnd_init _ _,
    Inv1.start_static himg hss rfl rfl, ?_, ⟨?_, hmem⟩, ⟨fits_empty rfl, hmf⟩, hg,
    ownOk_init (by simp [loadProg, Config.init]) hown0 _, heapCtr_of (fun _ _ _ _ h => by cases h), hfr0,
    [], s0 P.cap, hinit, .refl _⟩
  · exact ⟨E, rfl⟩
  · intro k m hk; unfold Memory.get? at hk; split at hk
    · cases hk
    · simp [loadProg, Config.init] at hk
  · intro k m hk; unfold Memory.get? at hk; split at hk
    · cases hk
    · simp [loadProg, Config.init] at hk

open Scc.Cert.Link in
/-- **The relation at the target's load** (`init_of_load` with the frames,
by `pre_loadS`). -/
theorem init_of_loadS {Λ : Scc.Sem.Layout} {G : Loc → Val → Prop} {own : OwnS} {I : InvS} {μ : Marks}
    {prog : Program} {secs : DataSecs}
    {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hwf : Λ.WF)
    (himg : imageOk Λ secs code = true)
    (hss : StaticSyms Λ secs code lsize name) (hw : wideIn prog = true) (hinit : P.init (s0 P.cap))
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    {rS : Range} {Tk : State → Prop} (htk0 : ¬ Tk (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    {t0 : T.M.Cfg} (hown0 : OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) [])
      t0.1.mem)
    (hg : MemInv G t0.1.mem) (h : loadParsed (kernel 1) E Λ prog secs = some t0) :
    ∃ s, (SrcSem.source P p).init s ∧ RS Λ P p G own I rS Tk μ cells ctr t0 s := by
  simp only [loadParsed] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    cases h
    refine ⟨s0 P.cap, hinit, .inl (pre_loadS himg hss hw hinit hst hfr0 (loadMem_in hwf hc.1.1.1.1) ?_ htk0
      hown0 hg)⟩
    rw [imageMem, wordsMem, wordsMem, ← List.map_append]
    exact initFits_words fun q hq => (List.mem_append.mp hq).elim (image_fit hwf q) (rodataWords_fit _ _ _ q)
  · cases h

/-! ## The step-wise simulation -/

open Scc.Cert.Link in
/-- **The step-wise simulation** at any depth (`stepSim` with the frames;
`PromSharedS` discharged by `promSharedS`). -/
theorem stepSimS {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ prog secs)
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (hP : HookOK P p) (hinit : P.init (s0 P.cap))
    (hN : NodesS Λ p ((TOn A ld rs).marks asm Λ) rd G own I) (hsafe : SrcSafeS P p I) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p ((TOn A ld rs).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hrd : ∀ w, rd w)
    (hwf : Λ.WF) (hG0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) :
    StepSim (TOn A ld rs) (SrcSem.source P p) Λ asm
      (RS Λ P p G own I rS Tk ((TOn A ld rs).marks asm Λ) cells ctr) where
  init _ h := init_of_loadS hwf himg hss hw hinit hst hfr0 htk0 (hown0 _ h) (hG0 _ h) (hl.symm.trans h)
  step _ _ _ _ _ h hs := r_stepS hP hN hsafe hT (promSharedS hP hN hsafe hrd hwf hGpl hT) hrd hwf hGpl h hs

/-! ## The explicit witness -/

/-- **The witness of a one-thread pair at any depth** (`wit` with the
frames): the environment map of `PlacedS` for every frame of thread 0. -/
def witS (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
    (envm : Nat → String → Nat → Option (WordPlace T.M.I.RegId)) (last : Nat) : Witness T.M where
  thr i := if i = 0 then some 0 else none
  lbl := lbl
  lsize := lsize
  ts := ts
  env i d x k := if i = 0 then envm d x k else none
  marked _ _ := False
  since _ := 0
  tsFrom _ := last

/-- **`Components` for a one-thread pair at any depth** (`components_one`
with the frames: every frame's environment by `PlacedS`). -/
theorem components_oneS (hwf : Λ.WF) {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isaLSE2} {th0 : TermRun.TTh}
    {lbl : Lbl} {lsize : Lsize} {ts : Nat → Option Nat} {rS : Range} {Tk : State → Prop}
    {hl : List (Nat × Range)} (hth : t.1.threads = #[th]) (hheld : t.2.held = hl) (hh : HeldOk Λ rS Tk th.st hl)
    (hmi : MemIn Λ t.1.mem) (hs0 : s.ths = #[th0]) (hpl : PlacedS Λ lbl th.st (Ctl.of th0) th0.stack)
    (hinv : Inv1 Λ lbl lsize ts th t.1.mem s.mem) (hown : OwnMsgs t.1.mem) :
    ∃ w : Witness T.M, Components T.M Λ w t s ∧ w.thr 0 = some 0 := by
  obtain ⟨envm, hrep, htot, himm⟩ := hpl
  have hsr : ∀ j rg, T.M.stackRange t j = some rg → j = 0 ∧ rg = rS ∧ Owned Λ rS th.st := by
    intro j rg h
    change Kernel.stackRangeOf abi t j = some rg at h
    unfold Kernel.stackRangeOf at h
    split at h
    · cases h
    · rename_i tt htt
      obtain ⟨rfl, rfl⟩ := get_one hth htt
      rw [hheld] at h
      rcases hh with ⟨rfl, -⟩ | ⟨rfl, -, ho⟩
      · simp at h
      · refine ⟨rfl, ?_, ho⟩
        simp only [List.find?_cons, List.find?_nil] at h
        split at h
        · exact (Option.some.inj h).symm
        · cases h
  have hs1 : ∀ {i} {th'}, s.ths[i]? = some th' → i = 0 ∧ th' = th0 := by
    intro i th' h
    rw [hs0] at h
    rcases i with _ | i
    · exact ⟨rfl, (Option.some.inj h).symm⟩
    · simp at h
  refine ⟨witS lbl lsize ts envm t.1.mem.last, Components.ofMemRelP (tp := []) (sp := []) hinv.mem
    { thr_total := ?_, thr_inj := ?_, thr_onto := ?_, env_rep := ?_, env_total := ?_,
      stack_pool := (fun j rg h => by obtain ⟨-, rfl, ho⟩ := hsr j rg h; exact ho.1),
      stack_disj := (fun j j' rg rg' hne h h' => absurd ((hsr j rg h).1.trans (hsr j' rg' h').1.symm) hne),
      stack_owned := (fun j rg h j' tt' htt a h8 h1 h2 => by
        obtain ⟨rfl, rfl, ho⟩ := hsr j rg h
        obtain ⟨rfl, rfl⟩ := get_one hth htt
        exact ⟨fun _ => rfl, fun _ => ho.2 a h8 h1 h2⟩),
      stack_private := (fun j rg h m hm hc => by
        obtain ⟨-, rfl, ho⟩ := hsr j rg h
        exact shared_not_pool hwf (memIn_msgs hmi m hm).addr (sub_contains ho.1 hc)),
      stack_marked := fun _ _ h => h.elim,
      stack_unmarked := fun _ _ _ _ _ _ _ _ _ _ h => h, env_imm := ?_ }
    (fun _ => rfl) (fun _ q hq => (hinv.mem.tq_le q hq).2) ?_, rfl⟩
  · intro i hi
    rw [hs0] at hi
    obtain rfl : i = 0 := by simpa using hi
    exact ⟨0, rfl, by rw [hth]; exact Nat.zero_lt_one⟩
  · intro i i' j h h'
    simp only [witS] at h h'
    by_cases hi : i = 0 <;> by_cases hi' : i' = 0
    · rw [hi, hi']
    · simp [hi'] at h'
    · simp [hi] at h
    · simp [hi] at h
  · intro j tt _ hj
    obtain ⟨rfl, -⟩ := get_one hth hj
    exact ⟨0, by rw [hs0]; exact Nat.zero_lt_one, rfl⟩
  · intro i th' j tt hi hj htt d e hd x ty ws hx k wd wp hwd hwp _hxf
    obtain ⟨rfl, rfl⟩ := hs1 hi
    simp only [witS, ite_true, Option.some.injEq] at hj
    subst hj
    obtain ⟨-, rfl⟩ := get_one hth htt
    simp only [witS] at hwp
    exact hrep d e hd x ty ws hx k wd wp hwd hwp
  · intro i th' hi d e xs hd hxs _hxf x hx ty ws hl k hk
    obtain ⟨rfl, rfl⟩ := hs1 hi
    obtain ⟨pl, hpl⟩ := htot d e xs hd hxs x hx ty ws hl k hk
    exact ⟨pl, by simp only [witS]; exact hpl⟩
  · intro i th' d e x k n hi hd hx
    obtain ⟨rfl, rfl⟩ := hs1 hi
    simp only [witS] at hx
    exact himm d e x k n hd hx
  · intro q hq m' hg
    rw [hown q m' hg]
    exact ⟨th, by rw [hth]; rfl, hq⟩

/-- **`RS` is explicit** (`r_components` with the frames). -/
theorem r_componentsS (hN : NodesS Λ p μ rd G own I) (hwf : Λ.WF) {rS : Range} {Tk : State → Prop} {t : T.M.Cfg}
    {s : TermRun.Cfg} (h : RS Λ P p G own I rS Tk μ cells ctr t s) :
    ∃ w : Witness T.M, Components T.M Λ w t ((SrcSem.source P p).core s) := by
  rcases h with ⟨th, th0, j, lbl, lsize, ts, hl, pm, _, hth, ⟨E, hk⟩, -, hh, -, -, hs0, -, -, hI, -, -, -, hinv,
      hown, hmi, -⟩ |
    ⟨th, th0, j, lbl, lsize, ts, hl, pm, o, hth, ⟨E, hk⟩, -, hh, hs0, -, -, hpl, hinv, hown, hmi, -⟩
  · exact (components_oneS hwf hth (by rw [hk]; rfl) hh hmi hs0
      (by have hpl := hN.place _ _ _ _ _ hI; exact hpl) hinv hown).imp fun _ h => h.1
  · exact (components_oneS hwf hth (by rw [hk]; rfl) hh hmi hs0 hpl hinv hown).imp fun _ h => h.1

/-! ## Progress -/

/-- **No promise at a `write`** at any depth (`WriteNoProm` over `PreS`). -/
def WriteNoPromS (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS)
    (I : InvS) (rS : Range) (Tk : State → Prop) (μ : Marks) (cells ctr : Nat) : Prop :=
  ∀ t s th, PreS Λ P p G own I rS Tk μ cells ctr t s → t.1.threads = #[th] → abi.atSys th.st = true →
    (∃ fd buf n, Kernel.callOf abi th = some (.write fd buf n)) → th.prom = []

/-- **Before the exit there is progress** at any depth (`pre_progress` with
the frames; off a system call by the row after the pair's frame run,
`NodesS.row`). -/
theorem pre_progressS (hN : NodesS Λ p μ rd G own I) {Ab : State → Prop} (hA : AbortPathS μ I Ab cells ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) (hwf : Λ.WF)
    (hsvc : WriteNoPromS Λ P p G own I rS Tk μ cells ctr)
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : PreS Λ P p G own I rS Tk μ cells ctr t s) : T.M.Progress μ t := by
  have hwnp := hsvc t s
  have hpre := h
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, hh, hwr, hcert, hs0, hσ, hp, hI, -, hw, hb,
    hinv, hown, hmi, -, -, -, -, -, hre⟩ := h
  have ht : t.1.threads[0]? = some th := by rw [hth]; rfl
  have hrk : t.2.runs 0 = true := by rw [hk]; rfl
  have hxk : t.2.exited = none := by rw [hk]; rfl
  have hruns : T.M.runs t 0 := ⟨⟨th, ht⟩, hxk, by show ¬ (t.2.runs 0 = false); rw [hrk]; simp⟩
  have hnh : th.halted = false := by
    by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
    · obtain ⟨a, ha, hpc⟩ := htk
      obtain ⟨sz, hcn⟩ := (hT.site _ _ _ _ _ hI a ha hpc).2.1
      simp [Thread.halted, Kraken.Promising.Lower.A64.exec_nop hcn]
    cases hs : abi.atSys th.st
    · obtain ⟨c₁, fs₁, -, -, hout⟩ := hN.row hI (fun a ha hpc => htk ⟨a, ha, hpc⟩)
      have := ExtRows.out_exec hs hout
      simp only [Thread.halted]
      cases he : isaLSE2.exec th.st
      · rw [he] at this; cases this
      · simp
    · obtain ⟨imm, sz, hc⟩ := hN.svc _ _ _ _ _ hI hs
      simp [Thread.halted, Kraken.Promising.Lower.A64.exec_svc hc]
  refine ⟨?_, .inr ⟨⟨0, hxk, hruns.2.2, th, ht, fun h => by rw [hnh] at h; cases h.1⟩, fun tid hl => ?_⟩⟩
  · rintro (⟨tid, m, ⟨⟨t1, ht1⟩, -, -⟩, hns, outs, hs, hm⟩ | (⟨tid, hf⟩ | ⟨tid, t1, e, ht1, -, -, hns, hex, htouch⟩))
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      have hs' : stepOne Arch.armv8 th 0 t.1.mem = some outs := by simp only [stepThread, ht1] at hs; exact hs
      cases hsy : abi.atSys th.st
      · by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
        · obtain ⟨a, ha, hpc⟩ := htk
          obtain ⟨sz, hcn⟩ := (hT.site _ _ _ _ _ hI a ha hpc).2.1
          exact Kraken.Promising.Lower.stepOne_silent_no_error Arch.armv8 0 (Kraken.Promising.Lower.A64.exec_nop hcn)
            (Kraken.Promising.Lower.silentTree_done _) hs' m hm
        · obtain ⟨c₁, fs₁, -, -, hout⟩ := hN.row hI (fun a ha hpc => htk ⟨a, ha, hpc⟩)
          exact ExtRows.out_no_error hsy hout hs' m hm
      · exact hns ⟨th, ht1, hsy⟩
    · unfold Kernel.faultAt at hf
      split at hf
      · rename_i t1 ht1
        obtain ⟨rfl, rfl⟩ := get_one hth ht1
        rw [hnh, Bool.or_false] at hf
        cases hsy : abi.atSys th.st
        · simp [hsy] at hf
        · obtain ⟨call, hd, -, hcl, -⟩ := hN.sysOk hT hI hsy
          rw [show Kernel.callOf abi th = some call from hd] at hf
          cases call with
          | clone st tl => exact hcl st tl rfl
          | _ => simp at hf
      · cases hf
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      rw [hk] at htouch
      exact hN.mapped _ _ _ _ _ hI hns e hex (touches_mono (fun _ _ h => mapped_KS h) htouch)
  · obtain ⟨-, -, t1, ht1, -⟩ := hl
    obtain ⟨rfl, rfl⟩ := get_one hth ht1
    by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
    · -- at the take site: the take
      obtain ⟨a, ha, hpc⟩ := htk
      obtain ⟨hntk, ⟨sz, hcn⟩, -, hsr, hsub, hpos, hrod, -⟩ := hT.site _ _ _ _ _ hI a ha hpc
      obtain rfl : hl = [] := by
        rcases hh with ⟨h, -⟩ | ⟨-, h, -⟩
        · exact h
        · exact absurd h hntk
      have hf : Kernel.fresh t (Kernel.siteRange abi th.st) = true := by
        rw [hsr]; exact fresh_of hwf hk hsub hpos hrod hmi
      exact ⟨[], _, .xfer .take hruns ⟨a, ha, th, ht, hpc⟩
        (Kernel.xfer_take (K := abi) Arch.armv8 1 ht hrk hxk (atNop_of_cellAt hcn) hf)⟩
    have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => htk ⟨a, ha, hpc⟩
    have hsite := no_siteS hN ht hI hnt
    cases hs : abi.atSys th.st
    · have hnsys : ¬ T.M.atSys t 0 := fun ⟨t2, ht2, h2⟩ => by
        cases (show some t2 = some th from ht2.symm.trans ht)
        have h3 : abi.atSys th.st = true := h2
        rw [hs] at h3; cases h3
      by_cases hpn : th.prom = []
      · obtain ⟨c₁, fs₁, -, -, hout⟩ := hN.row hI hnt
        obtain ⟨outs, o, hso, ho, hpo⟩ :=
          ExtRows.out_progress (A := Arch.armv8) (tid := 0) (mem := t.1.mem) hpn hb hs hout
        exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, certOkC_of_prom_nil hpo, rfl⟩)⟩
      · obtain ⟨t', mem', hr, hp'⟩ := hcert
        cases hr with
        | refl => exact absurd hp' hpn
        | step hs1 hrest =>
          obtain ⟨outs, o, hso, ho, rfl⟩ := hs1
          replace hso : stepOne Arch.armv8 th 0 t.1.mem = some outs :=
            (Kernel.certSem_step_of_not_site (x := t.2) (siteAt_noneS hN hI hnt) hs).symm.trans hso
          exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, ⟨t', mem', hrest, hp'⟩, rfl⟩)⟩
    · have hr := Kernel.ready_of abi (t := th) (c := t) hs hrk hxk
      obtain ⟨call, hd, hnx, hcl, -⟩ := hN.sysOk hT hI hs
      have hc : Kernel.callOf abi th = some call := hd
      have hsys : ∀ c', (kernel 1).sys μ 0 t [] c' → ∃ es c', T.M.Step μ 0 t es c' :=
        fun c' h => ⟨[], c', .sys hruns h (by simp) (by simp) (by simp)⟩
      by_cases hpn : th.prom = []
      rotate_left
      · -- with promises: no `write` (`WriteNoPromS`), none at `exit_group`; elsewhere `Kernel.sys_progress`
        have hsn := siteAt_noneS hN hI hnt
        cases call with
        | write fd buf n => exact absurd (hwnp th hpre hth hs ⟨fd, buf, n, hc⟩) hpn
        | exitGroup v => exact absurd (Kernel.prom_nil_of_exit hsn hs hd (.inr ⟨v, rfl⟩) hcert) hpn
        | exit => exact absurd rfl hnx
        | clone st tl => exact absurd rfl (hcl st tl)
        | _ =>
          obtain ⟨r, es, c', h, hca⟩ := Kernel.sys_progress ht hr hsn hc (fun _ _ _ h => by cases h)
            (fun _ _ h => by cases h) hpn hcert
          obtain rfl := Kernel.sysStep_ret_nil ht hc (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
            (fun h => by cases h) (fun _ h => by cases h) h
          exact hsys c' ⟨.ret r, h, hca⟩
      cases call with
      | write fd buf n =>
        by_cases hj : t.2.wr 0 = 0
        · exact hsys _ (Kernel.sys_writeIntr (K := abi) Arch.armv8 1 ht hr hpn hc hj)
        · exact hsys _ (Kernel.sys_writeRet (K := abi) Arch.armv8 1 ht hr hpn hc (Nat.pos_of_ne_zero hj))
      | futexWait => exact hsys _ (Kernel.sys_futexWait (K := abi) Arch.armv8 1 ht hr hpn hc)
      | futexWake k => exact hsys _ (Kernel.sys_futexWake (K := abi) Arch.armv8 1 ht hr hpn hc)
      | rtSigaction => exact hsys _ (Kernel.sys_rtSigaction (K := abi) Arch.armv8 1 ht hr hpn hc)
      | archSetFs a => exact hsys _ (Kernel.sys_archSetFs (K := abi) Arch.armv8 1 ht hr hpn hc)
      | exitGroup v =>
        by_cases hab : ∃ k a, μ.abortAt k = some a ∧ pcOf th.st = a
        · -- at an abort site: the abort
          obtain ⟨k, a, ha, hpc⟩ := hab
          obtain ⟨-, hv⟩ := hA.at_ _ _ _ _ _ hI k a ha hpc
          exact ⟨_, _, .sys hruns (Kernel.sys_exitGroupAbort (K := abi) Arch.armv8 1 k ht hr hpn hc (hv v hd))
            (by simp) (fun k' hk => by obtain rfl : k' = k := by simpa using hk
                                       exact ⟨a, ha, th, ht, hpc⟩) (fun e he => by simp at he)⟩
        · have hnoab : ∀ k a, μ.abortAt k = some a → ¬ T.M.AtAddr a t 0 := fun k a ha ⟨t2, ht2, hpc⟩ => by
            cases (show some t2 = some th from ht2.symm.trans ht); exact hab ⟨k, a, ha, hpc⟩
          exact ⟨_, _, .sys hruns (Kernel.sys_exitGroup (K := abi) Arch.armv8 1 ht hr hpn hc) (by simp)
            (fun k hk => by simp at hk) (fun _ _ => hnoab)⟩
      | exit => exact absurd rfl hnx
      | clone st tl => exact absurd rfl (hcl st tl)

/-- **After the exit there is progress** at any depth. -/
theorem post_progressS {rS : Range} {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    (h : PostS Λ P p rS Tk t s) : T.M.Progress μ t := by
  obtain ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩ := h
  exact Kernel.exited_progress abi (o := o) (by rw [hk])

/-- **There is progress from `RS`.** -/
theorem r_progressS (hN : NodesS Λ p μ rd G own I) {Ab : State → Prop} (hA : AbortPathS μ I Ab cells ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) (hwf : Λ.WF)
    (hsvc : WriteNoPromS Λ P p G own I rS Tk μ cells ctr)
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : RS Λ P p G own I rS Tk μ cells ctr t s) : T.M.Progress μ t :=
  h.elim (pre_progressS hN hA hT hwf hsvc) post_progressS

/-! ## Correctness -/

/-- The memory of a configuration `RS` relates is in the layout. -/
theorem r_memInS {rS : Range} {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    (h : RS Λ P p G own I rS Tk μ cells ctr t s) : MemIn Λ t.1.mem := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmi, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmi, _⟩ <;> exact hmi

/-! ## The abort clause -/

/-- **`TI` is kept by every step from `RS`** (`ti_step` with the frames). -/
theorem ti_stepS (hN : NodesS Λ p μ rd G own I) {Ab : State → Prop} (hA : AbortPathS μ I Ab cells ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es pre : List Ev} (h : RS Λ P p G own I rS Tk μ cells ctr t s)
    (hs : T.M.Step μ tid t es t') (hti : TI Ab pre t) : TI Ab (pre ++ es) t' := by
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩
  rotate_left
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hk]) hs).elim
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, -, hwr, -, hs0, hσ, hp, hI, -, hw, hb, hinv,
    hown, hmi, -⟩ := h
  obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
  obtain ⟨rfl, rfl⟩ := get_one hth ht1
  intro u hu hab
  by_cases hab0 : Ab th.st
  · exact List.mem_append_left _ (hti th ht1 hab0)
  refine List.mem_append_right _ ?_
  have hget : ∀ {v : Thread isaLSE2} {mem : Memory}, (t.1.withThread 0 v mem).threads[0]? = some u → u = v :=
    fun h => by
      simp only [Config.withThread, hth] at h
      exact (Option.some.inj h).symm
  by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
  · -- the take does not enter the phase (`AbortPathS.take`)
    obtain ⟨a, ha, hpc⟩ := htk
    obtain ⟨-, rfl⟩ := step_takeS hN hT ht1 hI ha hpc hs
    obtain rfl := hget hu
    exact absurd hab (hA.take _ _ _ _ _ hI hab0 a ha hpc _)
  have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => htk ⟨a, ha, hpc⟩
  rcases A64Ext.step_cases_site ht1 hw hinv hs (no_spawnS hN hT ht1 hI) (no_siteS hN ht1 hI hnt) with
    ⟨rfl, hns, outs, o, hso, ho, rfl, -, -⟩ | ⟨rfl, w, rfl, -, -, -⟩ | ⟨pk, hsys, -, -⟩
  · obtain rfl := hget hu
    exact absurd hab (stepOne_allInv Arch.armv8 hso ho (hA.instr _ _ _ _ _ hI hab0 hns)
      ⟨fun _ => trivial, fun _ _ => trivial⟩).1
  · obtain rfl := hget hu
    exact absurd hab hab0
  · obtain ⟨hr, call, hcall, hcases⟩ := Kernel.sysStep_cases (K := abi) ht1 hsys (wr_le hk hwr)
    rcases hcases with ⟨fd, buf, n, rd', b, u', rfl, rfl, -, -, hust, -, rfl⟩ |
      ⟨r, rfl, -, -, -, -, u', hu', hsu, -⟩ | ⟨-, -, -, rfl⟩ | ⟨v, rfl, ⟨-, -, rfl⟩ | ⟨k, -, -, -, rfl⟩⟩
    · obtain rfl := hget hu
      exact absurd (hust ▸ hab) hab0
    · have hsu' : u.st ∈ Kernel.certSuccs abi th.st call := Option.some.inj (hu'.symm.trans hu) ▸ hsu
      obtain ⟨fd, buf, n, rfl, hrf⟩ := hA.sys _ _ _ _ _ hI hab0 (atSys_of_ready hr) _ hcall _ hsu' hab
      obtain ⟨hc', hes⟩ := sysStep_write_ret ht1 hcall (wr_le hk hwr _ _ _ hcall) hsys
      have hu2 : u = Kernel.retThread abi th r := by rw [hc'] at hu; exact hget hu
      rw [hes (hrf r (by rw [hu2, Kernel.retThread_st]))]
      exact List.mem_singleton_self _
    all_goals
      obtain rfl : th = u := Option.some.inj (ht1.symm.trans hu)
      exact absurd hab hab0

/-- **`TI` along every run from `RS`.** -/
theorem ti_runS (hN : NodesS Λ p μ rd G own I) {Ab : State → Prop} (hA : AbortPathS μ I Ab cells ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hstep : ∀ {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev},
      RS Λ P p G own I rS Tk μ cells ctr t s → T.M.Step μ tid t es t' → ∃ s', RS Λ P p G own I rS Tk μ cells ctr t' s')
    {t t' : T.M.Cfg} {tr : List Ev} (hr : T.M.Run μ t tr t') :
    ∀ {s pre}, RS Λ P p G own I rS Tk μ cells ctr t s → TI Ab pre t → TI Ab (pre ++ tr) t' := by
  induction hr with
  | refl => intro s pre _ h; rwa [List.append_nil]
  | step hs _ ih =>
    intro s pre hR h
    obtain ⟨tid, hs⟩ := hs
    obtain ⟨s', hR'⟩ := hstep hR hs
    rw [← List.append_assoc]
    exact ih hR' (ti_stepS hN hA hT hR hs h)

/-- **Small environments in every frame: no big number** (`NoBigNumT`). -/
theorem noBigNumT_of_envSmallS {s : TermRun.Cfg} {i : Nat} {th : TermRun.TTh} (hi : s.ths[i]? = some th)
    (he : EnvSmallS th.env th.stack) : NoBigNumT i s := by
  intro th' hth' e hmem
  rw [hi] at hth'
  cases Option.some.inj hth'
  simp only [frameEnvs, List.mem_cons, List.mem_map] at hmem
  rcases hmem with rfl | ⟨f, hf, rfl⟩
  · exact he.1
  · exact he.2 f hf

/-- **The overflow abort is justified for `SrcSem.source P p` at any
depth** (`abortJustified_overflowS`; the gate `mainExit s = []` since thread
0's term is a `let`). -/
theorem abortJustified_overflow_sourceS {B : Budget} {tr : List Ev} {s : TermRun.Cfg} {th : TermRun.TTh}
    (hi : s.ths[0]? = some th) (hc : OvfReady (Ctl.of th)) (hσ : th.σs = []) (hp : th.promises = [])
    (hnb : NoBigNumT 0 s) : AbortJustified B (SrcSem.source P p) tr s 0 .overflow := by
  obtain ⟨es, s', hs, hb, hnb'⟩ := abortJustified_overflowS (p := p) (k := P.k) (arch := P.arch)
    (Sp := fun i c c' => SrcSem.SpawnBy P.cap i c c' ∨ P.hooks.ext i c c') (obsTrace := SrcSem.srcObs P.hooks.trace)
    (init := P.init) (B := B) (tr := tr) hi hc hσ hp hnb
  refine ⟨es, s', ⟨?_, hs⟩, hb, hnb'⟩
  obtain ⟨x, a, b, e, -, -, -, -, -, -, ht, -⟩ := hc
  unfold mainExit
  rw [hi]
  simp only [Ctl.of] at ht
  simp only [ht]

/-- **An abort from `RS` is justified** (`r_abort` with the frames): the
`writeErr` one by `TI`; the `overflow` one at any depth with every frame's
environment small (`abortJustified_overflow_sourceS`); the `heap` one with
the heap use within the budget's `cells` (`HeapCtr`, `hB`) and the next
label fresh (`FreshInv`, `abortJustified_heap_source`). -/
theorem r_abortS (hN : NodesS Λ p μ rd G own I) (hwf : Λ.WF) {Ab : State → Prop} (hA : AbortPathS μ I Ab cells ctr)
    {B : Budget} (hB : B.cells = cells) {rS : Range} {Tk : State → Prop} {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es tr : List Ev} {k : AbortKind} (h : RS Λ P p G own I rS Tk μ cells ctr t s)
    (hti : TI Ab tr t) (hs : T.M.Step μ tid t es t') (hk : Ev.abort k ∈ es) :
    ∃ w i, Components T.M Λ w t ((SrcSem.source P p).core s) ∧ w.thr i = some tid ∧
      AbortJustified B (SrcSem.source P p) tr s i k := by
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hx⟩, _⟩
  rotate_left
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hx]) hs).elim
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk'⟩, -, hh, -, -, hs0, hσ, hp, hI, -, -, -, hinv,
    hown, hmi, -, -, -, hhc, hfr, -⟩ := h
  obtain ⟨a, ha, t2, ht2, hpc⟩ := hs.abort_at hk
  obtain ⟨rfl, rfl⟩ := get_one hth ht2
  obtain ⟨w, hw, hw0⟩ := components_oneS hwf hth (by rw [hk']; rfl) hh hmi hs0
    (by have hpl := hN.place _ _ _ _ _ hI; exact hpl) hinv hown
  refine ⟨w, 0, hw, hw0, ?_⟩
  have hi : s.ths[0]? = some th0 := by rw [hs0]; rfl
  obtain ⟨⟨rfl, hab⟩ | ⟨rfl, hc, he⟩ | ⟨rfl, hheap⟩, -⟩ := hA.at_ _ _ _ _ _ hI k a ha hpc
  · exact hti th ht2 hab
  · exact abortJustified_overflow_sourceS hi hc hσ hp (noBigNumT_of_envSmallS hi he)
  · have hr := hheap (heapUse s) hhc
    exact abortJustified_heap_source hi (by rw [hB]; exact hr) hσ hp 
      (Spike.Lib.fresh_of_placed (fun m hmem => (hinv.mem.lbl_mem m hmem).imp fun _ h => h.1) hfr.fresh)

open Scc.Cert.Link in
/-- **`Correct` for a one-thread program at any call depth on a target on
the canonical AArch64 machine** (`correctKOn` with the frames: `stepSimS`,
`r_progressS`, `r_memInS`, `r_abortS` with `ti_runS` from `ti_load`,
`r_componentsS`); the budget's heap `cells` are the arena's (`hB`). -/
theorem correctKOnS {B : Budget} (hB : B.cells = cells) {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ prog secs)
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (hload : ∃ t0, (TOn A ld rs).load asm Λ = some t0) (hP : HookOK P p)
    (hinit : P.init (s0 P.cap))
    (hN : NodesS Λ p ((TOn A ld rs).marks asm Λ) rd G own I) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p ((TOn A ld rs).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hsvc : WriteNoPromS Λ P p G own I rS Tk ((TOn A ld rs).marks asm Λ) cells ctr)
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPathS ((TOn A ld rs).marks asm Λ) I Ab cells ctr)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata))) :
    Correct (TOn A ld rs) (SrcSem.source P p) Λ B asm := by
  have hsim := stepSimS (cells := cells) (ctr := ctr) hl himg hss hw hst hfr0 hP hinit hN hsafe hT htk0 hown0 hrd
    hwf hG0 hGpl
  have hps := promSharedS (cells := cells) (ctr := ctr) hP hN hsafe hrd hwf hGpl hT
  refine correct_of_stepSim hsim hwf hload (fun t0 tr t h0 hr => ?_)
    (fun t0 tr t tid es t' k s h0 hr _ hR hs hk => ?_)
    (fun t s hR => r_componentsS hN hwf hR)
  · obtain ⟨s, -, hR⟩ := hsim.reach h0 hr
    exact ⟨r_progressS hN hA hT hwf hsvc hR, inLayout_of_memIn (r_memInS hR)⟩
  · obtain ⟨s0', -, hR0⟩ := hsim.init t0 h0
    have hti := ti_runS hN hA hT
      (fun hR hs => let ⟨s', _, h'⟩ := r_stepS hP hN hsafe hT hps hrd hwf hGpl hR hs; ⟨s', h'⟩)
      hr hR0 (pre := []) (fun th h hab => absurd hab (ti_load hab0 (hl.symm.trans h0) th h))
    rw [List.nil_append] at hti
    exact r_abortS hN hwf hA hB hR hti hs hk

open Scc.Cert.Link in
/-- **`Correct` for a one-thread program at any call depth on the canonical
AArch64 target**: `correctKOnS` at `T`, the load by `load_of_parsed`. -/
theorem correctKS {B : Budget} (hB : B.cells = cells) {asm : String} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hpa : textProgram asm = .ok prog)
    (hd : dataSections asm = some secs) (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (hload : ∃ t0, T.load asm Λ = some t0) (hP : HookOK P p) (hinit : P.init (s0 P.cap))
    (hN : NodesS Λ p (T.marks asm Λ) rd G own I) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p (T.marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, T.load asm Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hsvc : WriteNoPromS Λ P p G own I rS Tk (T.marks asm Λ) cells ctr)
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, T.load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPathS (T.marks asm Λ) I Ab cells ctr)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata))) :
    Correct T (SrcSem.source P p) Λ B asm :=
  correctKOnS (A := String) (ld := T.load) (rs := T.resolve) hB (load_of_parsed (kernel 1) Entry.linux Λ hpa hd)
    himg hss hw hst hfr0 hload hP hinit hN hsafe hT htk0 hown0 hsvc hrd hwf hG0 hGpl hA hab0

end Spike.Lib.A64ConsumerS
