/-
A consumer of the per-construct judgement: `Correct` for the flag program
of the bridge spike, with the reader thread given by a `Seg` invariant.

`Spike/Bridge/Loop.lean` and `Spike/Bridge/LoopCorrect.lean` prove
`Correct` for a reader described by its Kraken event trees alone
(`LoopShape`) and a hand-written source side (`Spike/Bridge/LoopSrc.lean`).
Here the reader is any pair of fragments `Inv`, `Fin` with
`Reader p lbl F Inv Fin`: every pair of `Inv` takes one instruction
(`Out`) into `Inv` or the halted exit `Fin`, the source matching it, never
by a store, every load being of the flag. The relation (`RelS`) is
`RelL`'s, with the reader's phase the fragment (`SPhase`): the Kraken
thread's state and the source thread's control are a pair of `Inv` or
`Fin`. The simulation step (`sim_step_seg`) reads each case of `Out` once:

* `silent`: the Kraken side keeps memory, promises, forwarding bank and the
  flag's coherence view (`k_done_out`); the source side is the local run,
  lifted (`LocalRun.run`);
* `choice`: as `silent`, at the leaf the Kraken step took (`k_silent_out`,
  from `stepOne_silent_ok`);
* `load`: the Kraken side reads a message no flag write hides
  (`k_load_out`); the source side reads the related message (`load_read`,
  the generic form of `head_read`), which `rd` admits (`NumMS`, `NumRd`: the
  flag's memory holds numbers);
* `store`: excluded (`Reader.noStore`); `rtStore`: excluded (the runtime
  owns no address, `NumMS`).

The progress parts (`rspecS`) and the components (`componentsS`, from
where the fragments place the source words, `Place`) follow, and
`correctS` is `Correct`, as `correctL` states it, for the source program
`p` from `srcInitS c1`.
-/
import Spike.Lib.Src
import Spike.Bridge.LoopCorrect

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.Lower Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep
open Scc.Sem (SrcSem ExtMachine Target obs Correct Budget Components ValRep)
open Spike.Bridge

/-! ## The source half: a load of the flag -/

section Src

variable {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch}

/-- **The source load of the flag in closed form**: a thread at
`let x = load acq a in e` with `a` the flag reference. -/
theorem tstep_load (g : TermRun.G) (mem : WeakMem.Memory) (pairs : List Nat) (th : TermRun.TTh) {x : String}
    {a : At} {e : Expr} (ht : th.term = .let_ x (.load true a) e) (hev : TermRun.evalAt th.env a = some (fTy, [fW]))
    (hσ : th.σs = []) (hst : th.stack = []) :
    TermRun.tstep g mem pairs th =
      (Promises.stepLoad g.arch mem pairs (TermRun.mth (TermRun.stOf mem pairs th) fW fW fW) 1 flagA [0] true).map
        fun th' => (mem, pairs, { th with
          term := e
          env := (x, .int, [th'.regs 1]) :: th.env
          vs := th'.vs
          undefs := th.undefs + TermRun.countUndef [th'.regs 1] }) := by
  simp [TermRun.tstep, ht, TermRun.evalOp, hev, fTy, cellOf, TermRun.addrOf, fW, TermRun.cst, Promises.TVal.mk0,
    flagA, TermRun.accs, TermRun.loadUnits, TermRun.offs, TermRun.withS, TermRun.stOf, hσ, hst]
  generalize Promises.stepLoad _ _ _ _ _ _ _ _ = L
  induction L <;> simp_all

/-- **A source thread at a load of the flag reads** any message of the flag
its read bound does not hide (`head_read` for any thread, term and
environment). -/
theorem load_read (c : TermRun.Cfg) {i : Nat} {th : TermRun.TTh} (hi : c.ths[i]? = some th) {x : String} {a : At}
    {e : Expr} (ht : th.term = .let_ x (.load true a) e) (hev : TermRun.evalAt th.env a = some (fTy, [fW]))
    (hσ : th.σs = []) (hst : th.stack = []) {t : Nat} {m : WeakMem.Msg} (hm : c.mem[t]? = some m)
    (hl : m.loc = flagA) (hnh : WeakMem.hiddenFrom c.mem flagA t (Promises.readBoundOf arch th.vs 0 flagA) = false) :
    ∃ u', { c with ths := c.ths.set! i { th with
        term := e
        env := (x, .int, [⟨m.val, m.view, t⟩]) :: th.env
        vs := loadVS th.vs c.pairs t m.view
        undefs := u' } } ∈ TermRun.threadSteps p k arch c i := by
  have hlt : t < c.mem.size := by
    rcases Nat.lt_or_ge t c.mem.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hm
  have hm' : c.mem[t]! = m := by
    rw [getElem!_pos c.mem t hlt]; exact Option.some.inj ((Array.getElem?_eq_getElem hlt).symm.trans hm)
  have hdb : Promises.depBound (TermRun.mth (TermRun.stOf c.mem c.pairs th) fW fW fW).regs [0] = 0 := by
    simp [Promises.depBound, Promises.depView, Promises.depRts, TermRun.mth, TermRun.regsOf, fW, TermRun.cst,
      Promises.TVal.mk0]
  unfold TermRun.threadSteps
  rw [hi]
  simp only [tstep_load _ _ _ _ ht hev hσ hst, List.map_map]
  unfold Promises.stepLoad
  simp only [List.map_map]
  refine ⟨th.undefs + TermRun.countUndef [⟨m.val, m.view, t⟩],
    List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨List.mem_range.mpr hlt, ?_⟩, ?_⟩⟩
  · rw [hdb]
    simp only [WeakMem.readable, hm, hl, Option.elim, decide_true, Bool.true_and, Bool.not_eq_eq_eq_not,
      Bool.not_true]
    exact hnh
  · simp only [hm', Function.comp, ite_true]
    rfl

end Src

/-! ## The Kraken half: a load and a silent instruction -/

section KSteps

variable {I : ISA} (A : Arch) {F : BitVec 64}

/-- **A load of the flag** (Kraken side, `loop_head_out` for any tree of
this shape): memory, promises and forwarding bank unchanged; the thread at
`g v` for a value `v` read at a timestamp `ts` that no flag write hides
below the coherence view; without a forwarding entry the coherence view
rises to at least `ts`. -/
theorem k_load_out {tid : Nat} {t : Thread I} {mem : Memory} {q : Thread I × Memory} {kl : Kraken.LoadKind}
    {g : Val → I.State} (hex : I.exec t.st = some (.load kl false ⟨F, 8⟩ fun v => .done (g v)))
    (h : ThreadStep A tid (t, mem) q) :
    q.2 = mem ∧ q.1.prom = t.prom ∧ q.1.views.fwdb = t.views.fwdb ∧
      ∃ ts v, q.1.st = g v ∧ mem.read? ⟨F, 8⟩ ts = some v ∧
        mem.writeIn ⟨F, 8⟩ ts (t.views.getCoh ⟨F, 8⟩) = false ∧
        (t.views.fwdb = [] → max (t.views.getCoh ⟨F, 8⟩) ts ≤ q.1.views.getCoh ⟨F, 8⟩) := by
  obtain ⟨outs, o, hs, ho, rfl⟩ := h
  obtain ⟨st, c', hrun, hth, hm⟩ := (stepOne_ok_iff A tid hex).mp ⟨outs, o, hs, ho, rfl, rfl⟩
  rw [run_load_iff] at hrun
  obtain ⟨ts, v, hx, rfl⟩ := hrun
  have hp := readSuccs_prom A _ hx
  obtain ⟨ts', v', he, -, hv, hwi, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hk := (finishInstr_relKey hth).2
  have hcoh : o.thread.views.coh = (readNext A (instrViews t (I.deps t.st)) (ctx0 tid t mem) kl false ⟨F, 8⟩ false ts
      v).views.coh := by have := congrArg Views.coh hk; exact this
  have hfw : o.thread.views.fwdb = t.views.fwdb := by have := congrArg Views.fwdb hk; exact this
  refine ⟨hm, (finishInstr_relKey hth).1.trans hp, hfw, ts, v, finishInstr_st hth, hv, ?_, fun hf => ?_⟩
  · unfold Memory.writeIn at hwi ⊢
    rw [List.any_eq_false] at hwi ⊢
    intro i hi
    exact hwi i (List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp hi)
      (Nat.sub_le_sub_right (Nat.le_max_right _ _) _)))
  · have hgf : (ctx0 tid t mem).views.getFwd ⟨F, 8⟩ = none := by
      show (t.views.fwdb.find? _).map _ = none
      rw [hf]; rfl
    have := getCoh_readNext A (iv := instrViews t (I.deps t.st)) (kl := kl) (v := v) (ts := ts) hgf
    have hg : o.thread.views.getCoh ⟨F, 8⟩ = (readNext A (instrViews t (I.deps t.st)) (ctx0 tid t mem) kl false
        ⟨F, 8⟩ false ts v).views.getCoh ⟨F, 8⟩ := by
      unfold Views.getCoh; rw [hcoh]
    rw [hg]
    exact this

/-- **A silent instruction** (Kraken side, `loop_mid_out` for any `.done`
tree): memory, promises, forwarding bank and coherence views unchanged. -/
theorem k_done_out {tid : Nat} {t : Thread I} {mem : Memory} {q : Thread I × Memory} {s' : I.State}
    (hex : I.exec t.st = some (.done s')) (h : ThreadStep A tid (t, mem) q) :
    q.2 = mem ∧ q.1.prom = t.prom ∧ q.1.views.fwdb = t.views.fwdb ∧
      q.1.views.getCoh ⟨F, 8⟩ = t.views.getCoh ⟨F, 8⟩ ∧ q.1.st = s' := by
  obtain ⟨outs, o, hs, ho, rfl⟩ := h
  obtain ⟨st, c', hrun, hth, hmem⟩ := (stepOne_ok_iff A tid hex).mp ⟨outs, o, hs, ho, rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := (run_done_iff A tid _).mp hrun
  have hk := (finishInstr_relKey hth).2
  have hcoh : o.thread.views.coh = t.views.coh := by have := congrArg Views.coh hk; exact this
  have hfw : o.thread.views.fwdb = t.views.fwdb := by have := congrArg Views.fwdb hk; exact this
  exact ⟨hmem, (finishInstr_relKey hth).1, hfw, by unfold Views.getCoh; rw [hcoh], finishInstr_st hth⟩

/-- **An instruction with a choice of silent leaves** (an undefined flag):
as `k_done_out`, the thread at a leaf satisfying `P`. -/
theorem k_silent_out {tid : Nat} {t : Thread I} {mem : Memory} {q : Thread I × Memory} {tree : EvTree I.State}
    {P : I.State → Prop} (hex : I.exec t.st = some tree) (hs : SilentTree P tree)
    (h : ThreadStep A tid (t, mem) q) :
    q.2 = mem ∧ q.1.prom = t.prom ∧ q.1.views.fwdb = t.views.fwdb ∧
      q.1.views.getCoh ⟨F, 8⟩ = t.views.getCoh ⟨F, 8⟩ ∧ P q.1.st := by
  obtain ⟨outs, o, hso, ho, rfl⟩ := h
  obtain ⟨s', hP, hth, hmem⟩ := stepOne_silent_ok A tid hex hs ⟨outs, o, hso, ho, rfl, rfl⟩
  have hk := (finishInstr_relKey hth).2
  have hcoh : o.thread.views.coh = t.views.coh := by have := congrArg Views.coh hk; exact this
  have hfw : o.thread.views.fwdb = t.views.fwdb := by have := congrArg Views.fwdb hk; exact this
  exact ⟨hmem, (finishInstr_relKey hth).1, hfw, by unfold Views.getCoh; rw [hcoh], (finishInstr_st hth) ▸ hP⟩

/-- **A thread at a choice of silent leaves can step**, with no promise. -/
theorem choice_can_step {c : Config I} {t0 t1 : Thread I} (hc : c.threads = #[t0, t1]) (hp : t1.prom = [])
    {tree : EvTree I.State} {P : I.State → Prop} (hex : I.exec t1.st = some tree) (hs : SilentTree P tree) :
    ∃ c', StepSemInf A 1 c c' := by
  have ht : c.threads[1]? = some t1 := by rw [hc]; rfl
  obtain ⟨s, -, hstep⟩ := instrSemInf_silent_exists A 1 ht hex hs
  obtain ⟨th, hth⟩ := finishInstr_nonempty t1 (I.deps t1.st) (instrViews t1 (I.deps t1.st)) s (ctx0 1 t1 c.mem)
  exact ⟨_, .inl (hstep th hth (certOk_nil A (tid := 1) (mem := c.mem) (((finishInstr_relKey hth).1).trans hp)))⟩

end KSteps

/-! ## A reader given by a `Seg` invariant -/

/-- The flag's memory holds numbers: a source load binds a number. -/
def NumRd (w : TermRun.Word) : Prop := ∃ n, w.val = .num n

/-- The flag program's memory side: the source reads numbers (`NumRd`), and
the runtime owns no address (the program has only the flag), and no system
call is matched. -/
def NumMS {I : ISA} : MemSide I where
  rd := NumRd
  rt _ := False
  K := none
  G _ _ := True
  heap := 0
  ctr := 0
  units _ _ := 1
  off _ _ := 8
  cells := 0

/-- **A reader thread given by fragments**: every pair of `Inv` takes one
instruction into `Inv` or `Fin` (the body of a `Seg` from the reader's entry
to `Fin`), `Fin` has no next instruction, no instruction of `Inv` is a
store, exchange or buffer allocation, every load of `Inv` is of the flag reference, and the flag reference
represents `F`. -/
structure Reader {I : ISA} (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (F : BitVec 64) (Inv Fin : Frag I) :
    Prop where
  out : ∀ s c, Inv s c → Out p lbl NumMS (fun s c => Inv s c ∨ Fin s c) s c
  fin : ∀ s c, Fin s c → I.exec s = none
  noStore : ∀ s c, Inv s c → ∀ x a b e, c.term ≠ .let_ x (.store true a b none) e
  noXchg : ∀ s c, Inv s c → ∀ x sa u v e, ¬ XchgSite c x sa u v e
  noAlloc : ∀ s c, Inv s c → ∀ x a τ e, c.term ≠ .let_ x (.newBuf a τ) e
  flag : ∀ s c, Inv s c → ∀ x a e, c.term = .let_ x (.load true a) e → TermRun.evalAt c.env a = some (fTy, [fW])
  addr : ∀ n, ValRep lbl fW.val n → n = F.toNat

/-- The reader's phases on the Kraken side: some source control pairs with
the state. -/
def KPh {I : ISA} (Inv Fin : Frag I) (s : I.State) : Prop := ∃ c, Inv s c ∨ Fin s c

namespace Reader

variable {I : ISA} (A : Arch) {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {F : BitVec 64}
  {Inv Fin : Frag I} (hR : Reader p lbl F Inv Fin)
include hR

omit A in
/-- A reader's invariant is a segment to its exit. -/
theorem seg : Seg p lbl NumMS Inv Fin := ⟨Inv, fun _ _ h => h, hR.out⟩

omit A in
/-- A load of the reader is of the flag. -/
theorem load_addr {s : I.State} {c : Ctl} (hi : Inv s c) {x : String} {a : At} {e : Expr} {ty : Ty}
    {w : TermRun.Word} {B : BitVec 64} (ht : c.term = .let_ x (.load true a) e)
    (hev : TermRun.evalAt c.env a = some (ty, [w])) (hv : ValRep lbl w.val B.toNat) : ty = fTy ∧ w = fW ∧ B = F := by
  have h := hR.flag s c hi x a e ht
  rw [hev] at h
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl, BitVec.eq_of_toNat_eq (hR.addr _ hv)⟩

/-- **Every solo step of the reader keeps its memory, its promise set and
its phase**, for every value read. -/
theorem step {tid : Nat} {t : Thread I} {mem : Memory} {q : Thread I × Memory} (hP : KPh Inv Fin t.st)
    (h : ThreadStep A tid (t, mem) q) : q.2 = mem ∧ q.1.prom = t.prom ∧ KPh Inv Fin q.1.st := by
  obtain ⟨c, hi | hf⟩ := hP
  · cases hR.out _ _ hi with
    | silent s' c' hex _ hX =>
      obtain ⟨hm, hp, -, -, hst⟩ := k_done_out (F := F) A hex h
      exact ⟨hm, hp, c', hst ▸ hX⟩
    | choice P tr hex hs hX =>
      obtain ⟨hm, hp, -, -, hP⟩ := k_silent_out (F := F) A hex hs h
      obtain ⟨c', -, hx⟩ := hX _ hP
      exact ⟨hm, hp, c', hx⟩
    | load kl B g x a e ty w hex ht hev hv hX =>
      obtain ⟨-, -, rfl⟩ := hR.load_addr hi ht hev hv
      obtain ⟨hm, hp, -, ts, v, hst, -⟩ := k_load_out A hex h
      refine ⟨hm, hp, _, hst ▸ hX v (TermRun.cst (.num (v.setWidth 64).toNat)) ⟨_, rfl⟩ ?_⟩
      exact ⟨(v.setWidth 64).isLt, rfl⟩
    | store kr B V s' x a b e ty tb w wb hex ht =>
      exact absurd ht (hR.noStore _ _ hi _ _ _ _)
    | rtStore kr L V s' c' hex hrt _ => exact hrt.elim
    | rtLoad kl L g c' hex hrt => exact hrt.elim
    | sys K call hK => nomatch hK
    | holdLoad kl B g x sa u v e hex hx => exact absurd hx (hR.noXchg _ _ hi _ _ _ _ _)
    | xchgStore kr B V s' x sa u v e tv wv wold hex hx => exact absurd hx (hR.noXchg _ _ hi _ _ _ _ _)
    | ctrRmw _ _ _ _ _ _ _ _ _ _ hex hrt => exact hrt.elim
    | rtRmw _ _ _ _ _ hex hrt => exact hrt.elim
    | alloc s' B x a τ e ta ws k _ _ _ hex ht => exact absurd ht (hR.noAlloc _ _ hi _ _ _ _)
    | emit K _ _ _ _ hK => nomatch hK
  · exact absurd h (no_threadStep A (hR.fin _ _ hf))

/-- **The reader certifies only with no promise.** -/
theorem cert {tid : Nat} {t : Thread I} {mem : Memory} (hph : KPh Inv Fin t.st) (hc : CertOk A tid t mem) :
    t.prom = [] := by
  obtain ⟨t', mem', hrun, hp⟩ := hc
  suffices H : ∀ q r, ThreadNP A tid q r → KPh Inv Fin q.1.st → r.1.prom = q.1.prom by
    exact (H _ _ hrun hph).symm.trans hp
  intro q r hr
  induction hr with
  | refl => intro _; rfl
  | step hs _ ih =>
    intro hph
    obtain ⟨-, hp1, hph1⟩ := hR.step A hph hs
    exact (ih hph1).trans hp1

end Reader

/-! ## The relation and the simulation step -/

section Sim

variable {I : ISA} (A : Arch) {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {F : BitVec 64} {v1 : Val}
  {st0 sW : I.State} {Inv Fin : Frag I} {k : Promises.Knobs} {arch : WeakMem.Arch} {init : TermRun.Cfg → Prop}

/-- **The reader's phase**: no promise and no forwarding entry on either
side, the source views bounded (`VBound`), one frame and no type variables,
and the Kraken state and the source control a pair of `Inv` or `Fin`. -/
def SPhase (F : BitVec 64) (Inv Fin : Frag I) (t : Thread I) (th : TermRun.TTh) : Prop :=
  t.prom = [] ∧ t.views.fwdb = [] ∧ VBound th.vs (t.views.getCoh ⟨F, 8⟩) ∧ th.promises = [] ∧ th.σs = [] ∧
    th.stack = [] ∧ (Inv t.st (Ctl.of th) ∨ Fin t.st (Ctl.of th))

/-- **The relation**: `RelL` with the reader's phase `SPhase`. -/
def RelS (F : BitVec 64) (v1 : Val) (st0 sW : I.State) (Inv Fin : Frag I) (c : Config I) (s : TermRun.Cfg) :
    Prop :=
  ∃ t0 t1 th0 th1, c.threads = #[t0, t1] ∧ s.ths = #[th0, th1] ∧ WPhase st0 sW t0 th0 ∧ PromOK t0 c.mem ∧
    SPhase F Inv Fin t1 th1 ∧ MemRel F (· = v1) c.mem s.mem ∧ s.pairs = [] ∧ MV0 s.mem

/-- The source start configuration: the writer, and the reader at control
`c1`. -/
def srcInitS (c1 : Ctl) : TermRun.Cfg :=
  { mem := #[flagInit], ths := #[writerAt [], { term := c1.term, env := c1.env }], lbase := 1 }

theorem ctl_of_with (th : TermRun.TTh) {c : Ctl} (hc : c.hold = none) :
    Ctl.of { th with term := c.term, env := c.env } = c :=
  Ctl.of_with th hc

variable (hWS : WShape I F v1 st0 sW) (hR : Reader p lbl F Inv Fin)
include hWS hR

/-- **The simulation step, stutter form**, for a reader given by fragments:
the writer as in `sim_step_loop`; each reader instruction by the source run
its `Out` names. -/
theorem sim_step_seg {c c' : Config I} {s : TermRun.Cfg} {tid : Nat} (hRel : RelS F v1 st0 sW Inv Fin c s)
    (h : StepSemInf A tid c c') :
    ∃ s', (SrcSem.ofStep p k arch init).Run s [] s' ∧ RelS F v1 st0 sW Inv Fin c' s' := by
  obtain ⟨t0, t1, th0, th1, hc, hs, hW, hP, hRd, hM, hpairs, hmv⟩ := hRel
  have h0 : s.ths[0]? = some th0 := by rw [hs]; rfl
  have h1 : s.ths[1]? = some th1 := by rw [hs]; rfl
  rcases h with ⟨t, outs, o, ht, hst, ho, hcert, rfl⟩ | ⟨t, w, ht, hw, hcert, rfl⟩
  · rw [hc] at ht
    have hts : ThreadStep A tid (t, c.mem) (o.thread, o.mem) := ⟨outs, o, hst, ho, rfl⟩
    match tid, ht, hts, hcert with
    | 0, ht, hts, hcert =>
      change some t0 = some t at ht
      cases ht
      obtain ⟨sm, th', hstep, hW', hP', hM', hsm⟩ :=
        writer_sim A hWS (pr := p) (k := k) (arch := arch) h0 hW hP hM hts
      refine ⟨_, run_one (.inl ⟨hstep, certW A hWS ⟨th', getElem?_set!_self h0 th', hW', hP', hM'⟩ hcert⟩), ?_⟩
      refine ⟨o.thread, t1, th', th1, ?_, ?_, hW', hP', hRd, hM', hpairs, ?_⟩
      · show c.threads.set! 0 o.thread = _
        rw [hc]; rfl
      · show s.ths.set! 0 th' = _
        rw [hs]; rfl
      · show MV0 sm
        rcases hsm with rfl | rfl
        · exact hmv
        · exact hmv.push
    | 1, ht, hts, hcert =>
      change some t1 = some t at ht
      cases ht
      obtain ⟨hp1, hfw1, hvb, hpr1, hσ1, hst1, hph⟩ := hRd
      have hthr : ∀ t' : Thread I, c.threads.set! 1 t' = #[t0, t'] := by intro t'; rw [hc]; rfl
      have hths : ∀ th' : TermRun.TTh, s.ths.set! 1 th' = #[th0, th'] := by intro th'; rw [hs]; rfl
      rcases hph with hi | hf
      · cases hR.out _ _ hi with
        | silent s' c' hex hrun hX =>
          -- a silent instruction: the local run
          obtain ⟨hmem, hpr, hfw, hcoh, hstq⟩ := k_done_out (F := F) A hex hts
          have hm' : o.mem = c.mem := hmem
          refine ⟨_, hrun.run (k := k) (arch := arch) (init := init) h1 rfl rfl hσ1 hst1 hpr1, ?_⟩
          refine ⟨t0, o.thread, th0, _, hthr _, hths _, hW, by rw [hm']; exact hP,
            ⟨hpr.trans hp1, hfw.trans hfw1, by rw [hcoh]; exact hvb, hpr1, hσ1, hst1, ?_⟩,
            by rw [hm']; exact hM, hpairs, hmv⟩
          rw [hstq, ctl_of_with _ (hrun.hold rfl)]
          exact hX
        | choice Pl tr hex htr hX =>
          -- a choice of silent leaves: the local run from the leaf taken
          obtain ⟨hmem, hpr, hfw, hcoh, hPl⟩ := k_silent_out (F := F) A hex htr hts
          obtain ⟨c', hrun, hX'⟩ := hX _ hPl
          have hm' : o.mem = c.mem := hmem
          refine ⟨_, hrun.run (k := k) (arch := arch) (init := init) h1 rfl rfl hσ1 hst1 hpr1, ?_⟩
          refine ⟨t0, o.thread, th0, _, hthr _, hths _, hW, by rw [hm']; exact hP,
            ⟨hpr.trans hp1, hfw.trans hfw1, by rw [hcoh]; exact hvb, hpr1, hσ1, hst1, ?_⟩,
            by rw [hm']; exact hM, hpairs, hmv⟩
          rw [ctl_of_with _ (hrun.hold rfl)]
          exact hX'
        | load kl B g x a e ty w hex ht hev hv hX =>
          -- the load: one source load of the related message
          obtain ⟨rfl, rfl, rfl⟩ := hR.load_addr hi ht hev hv
          obtain ⟨hmem, hpr, hfw, ts, v, hstq, hrd, hwi, hcoh⟩ := k_load_out A hex hts
          obtain ⟨m, hsm, hl, hval⟩ := hM.read hrd
          obtain ⟨u', hstep⟩ := load_read (p := p) (k := k) (arch := arch) s h1 ht hev hσ1 hst1 hsm hl
            (hidden_false hM hwi hvb.readBound)
          have hmv0 : m.view = 0 := hmv _ _ hsm
          have hm' : o.mem = c.mem := hmem
          have hvlt : v.toNat < 2 ^ 64 := by
            rcases hM.read_val hrd with rfl | rfl
            · decide
            · rw [hWS.one]; decide
          refine ⟨_, run_one (.inl ⟨hstep, certified_nil (getElem?_set!_self h1 _) hpr1⟩), ?_⟩
          refine ⟨t0, o.thread, th0, _, hthr _, hths _, hW, by rw [hm']; exact hP,
            ⟨hpr.trans hp1, hfw.trans hfw1, ?_, hpr1, hσ1, hst1, ?_⟩, by rw [hm']; exact hM, hpairs, hmv⟩
          · show VBound (loadVS th1.vs s.pairs ts m.view) _
            rw [hpairs, hmv0]
            exact hvb.load (hcoh hfw1)
          · rw [hstq]
            refine hX v ⟨m.val, m.view, ts⟩ ⟨_, hval⟩ ?_
            show ValRep lbl m.val _
            rw [hval, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hvlt]
            exact ⟨hvlt, rfl⟩
        | store kr B V s' x a b e ty tb w wb hex ht =>
          exact absurd ht (hR.noStore _ _ hi _ _ _ _)
        | rtStore kr L V s' c' hex hrt _ => exact hrt.elim
        | rtLoad kl L g c' hex hrt => exact hrt.elim
        | sys K call hK => nomatch hK
        | holdLoad kl B g x sa u v e hex hx => exact absurd hx (hR.noXchg _ _ hi _ _ _ _ _)
        | xchgStore kr B V s' x sa u v e tv wv wold hex hx => exact absurd hx (hR.noXchg _ _ hi _ _ _ _ _)
        | ctrRmw _ _ _ _ _ _ _ _ _ _ hex hrt => exact hrt.elim
        | rtRmw _ _ _ _ _ hex hrt => exact hrt.elim
        | alloc s' B x a τ e ta ws k _ _ _ hex ht => exact absurd ht (hR.noAlloc _ _ hi _ _ _ _)
        | emit K _ _ _ _ hK => nomatch hK
      · exact absurd hts (no_threadStep A (hR.fin _ _ hf))
    | n + 2, ht, _, _ => simp at ht
  · rw [hc] at ht
    match tid, ht, hw, hcert with
    | 0, ht, hw, hcert =>
      change some t0 = some t at ht
      cases ht
      obtain ⟨-, th0', hb, hpe, hW', hP', hM'⟩ := writer_prom A hWS (pr := p) (k := k) (arch := arch) h0 hW hM hcert
      refine ⟨_, run_one hb, ?_⟩
      rw [hpe]
      refine ⟨promThread t0 c.mem w, t1, th0', th1, ?_, ?_, hW', hP', hRd, hM', hpairs, hmv.push⟩
      · show c.threads.set! 0 _ = _
        rw [hc]; rfl
      · show s.ths.set! 0 _ = _
        rw [hs]; rfl
    | 1, ht, hw, hcert =>
      change some t1 = some t at ht
      cases ht
      obtain ⟨-, -, -, -, -, -, hph⟩ := hRd
      have := hR.cert A (t := promThread t1 c.mem w) ⟨_, hph⟩ hcert
      simp at this
    | n + 2, ht, _, _ => simp at ht

omit hWS hR in
/-- The start configurations are related, the reader starting at a pair
`(st1, c1)` of `Inv`. -/
theorem rel_initS {st1 : I.State} {c1 : Ctl} (h1 : Inv st1 c1) (hh1 : c1.hold = none) :
    RelS F v1 st0 sW Inv Fin (Config.init [st0, st1] [(⟨F, 8⟩, 0)]) (srcInitS c1) := by
  refine ⟨Thread.init st0, Thread.init st1, writerAt [], _, rfl, rfl, .inl ⟨rfl, rfl⟩,
    fun _ h => by simp [Thread.init] at h, ⟨rfl, rfl, ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩, rfl, rfl,
      rfl, .inl ((Ctl.of_eq (th := { term := c1.term, env := c1.env }) rfl rfl hh1).symm ▸ h1)⟩,
    MemRel.start, rfl, ?_⟩
  intro i m hm
  match i, hm with
  | 0, hm => cases hm; rfl
  | n + 1, hm => simp [srcInitS] at hm

/-- **The `Sim.sim` clause, with trace equality**, for a reader given by
fragments. -/
theorem sim_clause_seg {st1 : I.State} {c1 : Ctl} (h1 : Inv st1 c1) (hh1 : c1.hold = none)
    (rv : I.State → I.RegId → BitVec 64)
    (pl : I.State → BitVec 64 → Option (BitVec 64)) (Λ : Scc.Sem.Layout) (μ : Scc.Sem.Marks) :
    ∀ t0 tr t, (Target.ofBase I A rv pl).load (asmOf st0 st1 F) Λ = some t0 →
      (Target.ofBase I A rv pl).M.Run μ t0 tr t →
      ∃ tr' s, (SrcSem.ofStep p k arch (· = srcInitS c1)).Reach tr' s ∧ RelS F v1 st0 sW Inv Fin t.1 s ∧
        obs tr = tr' :=
  sim_clause_stutter A (RelS F v1 st0 sW Inv Fin) (fun _ _ _ _ hR' h => sim_step_seg A hWS hR hR' h) rfl
    (rel_initS h1 hh1) rv pl Λ μ

end Sim

/-! ## Progress, the components, `Correct` -/

section Correct

variable {I : ISA} (A : Arch) {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {F : BitVec 64} {v1 : Val}
  {st0 sW : I.State} {Inv Fin : Frag I}

/-- **Where the fragments place the source words**: register `rF` holds the
flag's address in both threads, and the reader's environment is `f` bound
(`envF`) or also `r` bound to a number whose low 64 bits are in `rR`. -/
structure Place (rv : I.State → I.RegId → BitVec 64) (F : BitVec 64) (st0 sW : I.State) (rF rR : I.RegId)
    (Inv Fin : Frag I) : Prop where
  f0 : rv st0 rF = F
  fW : rv sW rF = F
  frame : ∀ s c, Inv s c ∨ Fin s c → rv s rF = F ∧ (c.env = envF ∨ ∃ (v : Val) (w : TermRun.Word),
    c.env = ("r", .int, [w]) :: envF ∧ w.val = .num v.toNat ∧ v.toNat < 2 ^ 64 ∧ rv s rR = v.setWidth 64)

variable (hR : Reader p lbl F Inv Fin)
include hR

/-- **The reader meets `RSpec`.** -/
theorem rspecS : RSpec A F v1 (KPh Inv Fin) where
  step {t mem q} hP hts := hR.step A (q := q) hP hts
  cert {t mem} hP hc := hR.cert A hP hc
  ok {t mem outs} hP hs' m := by
    obtain ⟨c, hi | hf⟩ := hP
    · cases hR.out _ _ hi with
      | silent s' c' hex => exact stepOne_no_error A hex (runTree_done_ok A _ _ _ _) hs' m
      | choice P tr hex hs => exact stepOne_silent_no_error A _ hex hs hs' m
      | load kl B g x a e ty w hex => exact stepOne_no_error A hex (runTree_load_ok A _ _ _ _ _ _) hs' m
      | store kr B V s' x a b e ty tb w wb hex ht => exact absurd ht (hR.noStore _ _ hi _ _ _ _)
      | rtStore kr L V s' c' hex hrt _ => exact hrt.elim
      | rtLoad kl L g c' hex hrt => exact hrt.elim
      | sys K call hK => nomatch hK
      | holdLoad kl B g x sa u v e hex hx => exact absurd hx (hR.noXchg _ _ hi _ _ _ _ _)
      | xchgStore kr B V s' x sa u v e tv wv wold hex hx => exact absurd hx (hR.noXchg _ _ hi _ _ _ _ _)
      | ctrRmw _ _ _ _ _ _ _ _ _ _ hex hrt => exact hrt.elim
      | rtRmw _ _ _ _ _ hex hrt => exact hrt.elim
      | alloc s' B x a τ e ta ws k _ _ _ hex ht => exact absurd ht (hR.noAlloc _ _ hi _ _ _ _)
      | emit K _ _ _ _ hK => nomatch hK
    · have hex : I.exec t.st = none := hR.fin _ _ hf
      simp [stepOne, hex] at hs'
  can {c t0 t1} hc hM hp hP hh := by
    obtain ⟨c1, hi | hf⟩ := hP
    · cases hR.out _ _ hi with
      | silent s' c' hex => exact done_can_step A hc hp hex
      | choice P tr hex hs => exact choice_can_step A hc hp hex hs
      | load kl B g x a e ty w hex ht hev hv =>
        obtain ⟨-, -, rfl⟩ := hR.load_addr hi ht hev hv
        exact load_can_step A hc hM hp hex
      | store kr B V s' x a b e ty tb w wb hex ht => exact absurd ht (hR.noStore _ _ hi _ _ _ _)
      | rtStore kr L V s' c' hex hrt _ => exact hrt.elim
      | rtLoad kl L g c' hex hrt => exact hrt.elim
      | sys K call hK => nomatch hK
      | holdLoad kl B g x sa u v e hex hx => exact absurd hx (hR.noXchg _ _ hi _ _ _ _ _)
      | xchgStore kr B V s' x sa u v e tv wv wold hex hx => exact absurd hx (hR.noXchg _ _ hi _ _ _ _ _)
      | ctrRmw _ _ _ _ _ _ _ _ _ _ hex hrt => exact hrt.elim
      | rtRmw _ _ _ _ _ hex hrt => exact hrt.elim
      | alloc s' B x a τ e ta ws k _ _ _ hex ht => exact absurd ht (hR.noAlloc _ _ hi _ _ _ _)
      | emit K _ _ _ _ hK => nomatch hK
    · simp [Thread.halted, hR.fin _ _ hf] at hh

variable {rv : I.State → I.RegId → BitVec 64} {pl : I.State → BitVec 64 → Option (BitVec 64)} {rF rR : I.RegId}

omit hR in
variable (rv pl) in
/-- **The components of `RelS` hold**, with the straight-line program's
`witness`. -/
theorem componentsS (hone : v1.toNat = 1) (hpl : Place rv F st0 sW rF rR Inv Fin) {Λ : Scc.Sem.Layout}
    (hΛ : FlagIn Λ F) {t : (ExtMachine.ofBase I A rv pl).Cfg} {s : TermRun.Cfg}
    (hRel : RelS F v1 st0 sW Inv Fin t.1 s) :
    Components (ExtMachine.ofBase I A rv pl) Λ (witness A rv pl F rF rR) t s := by
  obtain ⟨t0, t1, th0, th1, hc, hs, hW, -, ⟨-, -, -, -, -, hst, hph⟩, hM, -, -⟩ := hRel
  obtain ⟨hf, he⟩ := hpl.frame _ _ hph
  exact components_of hpl.f0 hpl.fW hone hΛ hc hs hW ⟨hst, hf, he⟩ hM

variable {st1 : I.State} {c1 : Ctl} (hWS : WShape I F v1 st0 sW) (h1 : Inv st1 c1)
include hWS h1

/-- **Progress** of a reader given by fragments. -/
theorem progressOfS (rv : I.State → I.RegId → BitVec 64) (pl : I.State → BitVec 64 → Option (BitVec 64)) :
    ProgressOf A rv pl st0 st1 F := fun _ hre _ hμ =>
  progress_of_base A hμ (baseProgressG A hWS (rspecS A hR)
    (tinvG_reach A hWS (rspecS A hR) hre (tinvG_init ⟨_, .inl h1⟩)))

/-- **`Correct` for a reader given by fragments**, every clause of `Sim`
discharged: the existing machine as a target, loading the writer's and the
reader's start states and the flag's initial write; the source program `p`
from `srcInitS c1`, any knobs and memory model, any budget. -/
theorem correctS {k : Promises.Knobs} {arch : WeakMem.Arch} (hpl : Place rv F st0 sW rF rR Inv Fin)
    {Λ : Scc.Sem.Layout} (hΛ : FlagIn Λ F) (hwf : Λ.WF) (B : Budget) (hh1 : c1.hold = none) :
    Correct (Target.ofBase I A rv pl) (SrcSem.ofStep p k arch (· = srcInitS c1)) Λ B (asmOf st0 st1 F) := by
  refine ⟨{
    R := fun t s => RelS F v1 st0 sW Inv Fin t.1 s
    layout := hwf
    start := ⟨_, srcInitS c1, rfl, rfl, rel_initS h1 hh1⟩
    progress := ?_
    sim := fun t0 tr t h0 hr => ?_
    abort := ?_
    explicit := fun t s hRel => ⟨witness A rv pl F rF rR, componentsS A rv pl hWS.one hpl hΛ hRel⟩ }⟩
  · intro t0 tr t h0 hr
    obtain ⟨-, s, -, hRel, -⟩ := sim_clause_seg A hWS hR (k := k) (arch := arch) h1 hh1 rv pl Λ _ t0 tr t h0
      hr
    cases h0
    obtain ⟨-, hre⟩ := ExtMachine.ofBase_run_inv hr
    obtain ⟨-, -, -, -, -, -, -, -, -, hM, -, -⟩ := hRel
    exact ⟨progressOfS A hR hWS h1 rv pl t hre _ (fun _ => rfl), inLayout_of A hΛ hM⟩
  · obtain ⟨tr', s, hs, hRel, he⟩ := sim_clause_seg A hWS hR (k := k) (arch := arch) h1 hh1 rv pl Λ _ t0 tr t h0
      hr
    exact ⟨tr', s, hs, hRel, he ▸ List.prefix_refl _⟩
  · intro t0 tr t tid es t' ak _ _ hs hab
    obtain ⟨rfl, -⟩ := ExtMachine.ofBase_step_inv hs
    cases hab

end Correct

end Spike.Lib
