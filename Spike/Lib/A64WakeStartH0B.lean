/-
**`RootOpen.hst0` from the start's segment** (wake.w, AArch64; H0 parts
B, D, E): the root's start segment, from the start pair (the loaded thread,
`wakeTh0`'s control, no frames) inside `W0W` under `TakeCKS` at `msBot`,
from `StartH0G.wake_start_wc_h0W`'s segment (at `c0W`, inside `WS` under the
take `PhRec.K`, from `_start`'s node to `wc_main`'s heap abort) and the heap
abort's segment (to no exit).

- `Out.prefix_done`, `SegW.prefix_done` (generic): a row from `c` is one from
  `c'` when `c'` runs locally to `c` and the instruction is silent (`done`,
  off a system call, no hold); a segment from `P` is one from the pairs
  whose control so runs into `P`.
- `SegWS.mono_W`, `SegWS.mono_K` (generic): `SegW.mono_W`/`mono_K` at
  frames.
- `LocalStepS.det`, `FrameStep.eq_loc`: a local step's successor is unique;
  a frame step of a control off a call and a `ret` is its local step.
- `runWf_th0`: `RunWf` at `wakeTh0`'s control (its frame runs pass
  `cBodyW` to `c0W`, `c0W_ctl`).
- `ws_th0`: `WS` at `wakeTh0`'s control from `WS` at `c0W` at a silent state
  (`PlacedSE` there given, the arena's writes vacuous, `c0W` neither an
  overflow nor a crossing allocation).
- `entry_atW`, `exec_start`, `atSys_start`, `site_ne_start`: the loaded
  thread at `_start`'s node at `ofPlaceW` (`LowerA64.entry_atECW`'s port),
  its `b scc_rt_start` silent, off a system call and off the take site.
- `QabW`, `W0S`, `takeCKS_iff`: `wake_start_wc_h0W`'s exit at `msBot E []`,
  `W0` at the start's marks (the heap abort stub's fragment), the take at
  `aW` as `PhRec.K` at `X0W`'s states.
- `hst0_of`: `RootOpen.hst0` from `wake_start_wc_h0W`'s segment (`hG`), the
  heap abort's (`hC`, from `QabW` at `[]` to no exit inside `W0S` under
  `PhRec.K`), and `wakeTh0`'s placement (`hplS`).
-/
import Spike.Lib.A64WakeRoot
import Spike.Lib.A64WakeStartH0G
import Spike.Lib.LowerA64.Closed2AtWA
import Spike.Lib.A64DmemPrivPlace

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising

section Gen

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}

/-- **A silent row from a control `c` is one from any `c'` running locally
to `c`**: the instruction a `done` (`hd`) off a system call (`hsys`), `c`
holding nothing. -/
theorem Out.prefix_done {X : Frag I} {s : I.State} {c c' : Ctl} (h : Out p lbl ms X s c) {s1 : I.State}
    (hd : I.exec s = some (.done s1)) (hsys : ∀ K, ms.K = some K → K.atSys s = false)
    (hr : LocalRun p c' c) (hc : c.hold = none) : Out p lbl ms X s c' := by
  cases h with
  | silent s' c'' he hr' hx => exact .silent s' c'' he (hr.trans hr') hx
  | choice P t he hs hx =>
    exact .choice P t he hs fun s' hp => let ⟨c'', hr', h⟩ := hx s' hp; ⟨c'', hr.trans hr', h⟩
  | load _ _ _ _ _ _ _ _ he => nomatch hd.symm.trans he
  | store _ _ _ _ _ _ _ _ _ _ _ _ he => nomatch hd.symm.trans he
  | rtStore _ _ _ _ _ he => nomatch hd.symm.trans he
  | rtLoad _ _ _ _ he => nomatch hd.symm.trans he
  | rtRmw _ _ _ _ _ he => nomatch hd.symm.trans he
  | sys K _ hK ha => rw [hsys K hK] at ha; cases ha
  | holdLoad _ _ _ _ _ _ _ _ he => nomatch hd.symm.trans he
  | xchgStore _ _ _ _ _ _ _ _ _ _ _ _ he => nomatch hd.symm.trans he
  | ctrRmw _ _ _ _ _ _ _ he => nomatch hd.symm.trans he
  | alloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh => rw [hc] at hh; cases hh
  | newStore _ _ _ _ _ _ _ _ _ _ _ _ he => nomatch hd.symm.trans he
  | emit K _ _ _ _ hK ha => rw [hsys K hK] at ha; cases ha
  | fence _ _ _ he => nomatch hd.symm.trans he

variable {W : Frag I} {K : I.State → I.State → Prop} {P P' Q : Frag I}

/-- **A segment from the pairs running locally into its entry**: each pair
`(s, c')` of `P'` has a `c` with `(s, c)` in `P`, `c'` running locally to
`c` (no hold), the instruction at `s` silent, off a system call and not
moved from outside, and `W` moving from `(s, c)` to `(s, c')`. -/
theorem SegW.prefix_done (h : SegW W K p lbl ms P Q)
    (hP : ∀ s c', P' s c' → ∃ c, P s c ∧ LocalRun p c' c ∧ c.hold = none ∧ (∃ s1, I.exec s = some (.done s1)) ∧
      (∀ s', ¬ K s s') ∧ (∀ Ks, ms.K = some Ks → Ks.atSys s = false) ∧ (W s c → W s c')) :
    SegW W K p lbl ms P' Q := by
  obtain ⟨inv, hs, hw, ho⟩ := h
  refine ⟨fun s c => inv s c ∨ P' s c, fun s c h => .inr h, ?_, ?_⟩
  · rintro s c (h | h)
    · exact hw s c h
    · obtain ⟨c0, hp0, -, -, -, -, -, hW⟩ := hP s c h
      exact hW (hw s c0 (hs s c0 hp0))
  · rintro s c (h | h)
    · exact kout_out_mono (ho s c h) fun s c h => h.imp_left .inl
    · obtain ⟨c0, hp0, hr, hh, ⟨s1, hd⟩, hk, hsys, -⟩ := hP s c h
      exact ⟨fun _ => (((ho s c0 (hs s c0 hp0)).1 hk).prefix_done hd hsys hr hh).mono
        fun s c h => h.imp_left .inl, KOut.none hk⟩

/-- `SegWS` inside a weaker predicate. -/
theorem SegWS.mono_W {W W' : FragS I} {K : I.State → I.State → Prop} {ms : List TermRun.Frame → MemSide I}
    {P Q : FragS I} (h : SegWS W K p lbl ms P Q) (hW : ∀ s c fs, W s c fs → W' s c fs) : SegWS W' K p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, fun s c fs h => hW s c fs (hw s c fs h), ho⟩

/-- `SegWS` under outside moves `K'` that move the predicate's states as
`K` does. -/
theorem SegWS.mono_K {W : FragS I} {K K' : I.State → I.State → Prop} {ms : List TermRun.Frame → MemSide I}
    {P Q : FragS I} (h : SegWS W K p lbl ms P Q) (hK : ∀ s c fs, W s c fs → ∀ s', K' s s' ↔ K s s') :
    SegWS W K' p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c fs h =>
    ⟨fun hn => (ho s c fs h).1 fun s' hk => hn s' ((hK s c fs (hw s c fs h) s').2 hk),
      fun s' hk => (ho s c fs h).2 s' ((hK s c fs (hw s c fs h) s').1 hk)⟩⟩

end Gen

/-- **A local step's successor is unique**. -/
theorem LocalStepS.det {p : Prog} {c c1 c2 : Ctl} (h1 : LocalStepS p c c1) (h2 : LocalStepS p c c2) : c1 = c2 := by
  let g : TermRun.G := { p := p, k := {}, arch := .arm, n := 0, i := 0, lbase := 0 }
  let th : TermRun.TTh := { term := c.term, env := c.env }
  have e := (h1.2 g #[] [] th rfl rfl rfl rfl).symm.trans (h2.2 g #[] [] th rfl rfl rfl rfl)
  obtain ⟨t1, e1, o1⟩ := c1
  obtain ⟨t2, e2, o2⟩ := c2
  have ho1 : o1 = none := h1.1
  have ho2 : o2 = none := h2.1
  simp only [List.cons.injEq, Prod.mk.injEq, TermRun.TTh.mk.injEq, th, and_true, true_and] at e
  rw [e.1, e.2, ho1, ho2]

/-- **A frame step of a control off a call and a `ret` is its local step**. -/
theorem FrameStep.eq_loc {p : Prog} {c c1 : Ctl} {fs : List TermRun.Frame} {q : Ctl × List TermRun.Frame}
    (h : FrameStep p (c, fs) q) (hl : LocalStepS p c c1)
    (hc : ∀ x f is a e, c.term ≠ .let_ x (.call f is a []) e) (hr : ∀ a, c.term ≠ .ret a) : q = (c1, fs) := by
  cases h with
  | loc h' => rw [hl.det h']
  | call hc' => exact (hc _ _ _ _ _ hc').elim
  | ret hc' => exact (hr _ hc').elim

end Spike.Lib

/-! ## The loaded thread at `_start` (at `ofPlaceW`) -/

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64.Rt (RuntimeLayout rtF entryR)
open Scc.Sem Scc.Sem.A64

section EntryW

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : PlaceW pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **The loaded thread is at `_start`** at `ofPlaceW` (A1's `_start` at the
code base), at any entry state `E`. -/
theorem hpc_ofPlaceW (E : Entry) :
    (Scc.Sem.A64.threadAt E (RuntimeLayout.ofPlaceW h i).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceW h i).Λ o.secs.rodata)).st.2 =
      (RuntimeLayout.ofPlaceW h i).lab "_start" := by
  have h1 := h.a1
  simp only [Scc.Cert.PlaceOK.A64.a1, Bool.and_eq_true, decide_eq_true_eq] at h1
  have hst : Scc.Cert.Link.A64.codeOf (RuntimeLayout.ofPlaceW h i).Λ.code.lo o.prog "_start" =
      some (RuntimeLayout.ofPlaceW h i).Λ.code.lo := h1.2
  exact (Scc.Cert.Rt.A64.label_threadAt_of_codeOf_below (E := E)
    (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW_below h i hst) hst).symm

set_option maxRecDepth 100000 in
/-- **The loaded thread is at `_start`'s node with the control `c`** at
`ofPlaceW` (`entry_atECW`'s port): on the entry stack `entryR E` of an
admissible entry state, no word of the link in the entry stack, the
runtime's words unloaded. -/
theorem entry_atW (c : Ctl) {E : Entry} (hE : E.Ok (RuntimeLayout.ofPlaceW h i).Λ) :
    At (RuntimeLayout.ofPlaceW h i).exe (RuntimeLayout.ofPlaceW h i).endPc (entryR E)
      (fun m => Spike.Lib.DmemPriv.WordsNoneP (RuntimeLayout.ofPlaceW h i).Λ m.dmem ∧
        rtF (RuntimeLayout.ofPlaceW h i) m)
      (Ret0.entryN (RuntimeLayout.ofPlaceW h i).lab c)
      (Scc.Sem.A64.threadAt E (RuntimeLayout.ofPlaceW h i).Λ.code.lo o.prog
        (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceW h i).Λ o.secs.rodata)) c := by
  refine ⟨rfl, Scc.Cert.Rt.A64.endPc_threadAt_below _ _ _ _, rfl, hpc_ofPlaceW h i E,
    ⟨{ SP := UInt64.ofNat E.sp }, _, fun k =>
    BitVec.ofInt 64 ((Mem.loadInt E.stackMem ((entryR E).addr k) 8).getD 0)⟩,
    ⟨rfl, rfl, ?_, ?_⟩,
    ⟨Spike.Lib.DmemPriv.wordsNoneP_stackMem (Spike.Lib.PlaceW.wf_link_of_placeW i h) hE.1,
      Spike.Lib.A64.Rt.rtF_stackMem _ hE rfl⟩, rfl⟩
  · intro r k hr
    rcases r with x | _
    · simp [Ret0.entryN, A64.Abort.oE, SO.get, lk] at hr
    · simp only [Ret0.entryN, A64.Abort.oE, SO.get, Option.some.injEq] at hr
      subst hr
      dsimp only
      show (UInt64.ofNat E.sp).toBitVec = BitVec.ofNat 64 E.sp + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl
  · intro k hk
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (Spike.Lib.A64.Rt.stack_wordE hE hk)
    refine ⟨j, hj, ?_⟩
    show _ = BitVec.ofInt 64 ((Mem.loadInt E.stackMem _ 8).getD 0)
    rw [hj]; rfl

end EntryW

end Spike.Lib.LowerA64

/-! ## `wakeTh0`'s control -/

namespace Spike.Lib.A64.WakePh.StartH0B

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram pcOf abi)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeKS TakeCKS CloneErrK)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.WakeWf (RunWf DtW X0W)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Ret0 (pinA entryN)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (wX)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.DmemPriv (WordsNone WordsNoneP)
open Spike.Lib (Arena FragS Frag SegW SegWS Ctl LocalRun LocalStepS FrameRun FrameStep)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeC0 (c0W cBodyW)
open Spike.Lib.WakePreAsm (wakeTh0)
open Spike.Lib.WakeOPremW (W0W)

/-- `wakeTh0`'s control (the start pair's, `WakeRoot.StartP`). -/
abbrev cS : Ctl := Ctl.of wakeTh0

theorem cS_term : cS.term = .tail "main" [] (.var "me") := rfl

/-- **The frame runs from `wakeTh0`'s control** stop at it or at `cBodyW`,
or pass `c0W`. -/
theorem frameRun_th0 {q : Ctl × List TermRun.Frame} (h : FrameRun wakeSrc (cS, []) q) :
    q = (cS, []) ∨ q = (cBodyW, []) ∨ FrameRun wakeSrc (c0W, []) q := by
  cases h with
  | refl => exact .inl rfl
  | step h1 h2 =>
    rw [h1.eq_loc WakeC0.step_tail (fun _ _ _ _ _ h => by rw [cS_term] at h; cases h)
      (fun _ h => by rw [cS_term] at h; cases h)] at h2
    cases h2 with
    | refl => exact .inr (.inl rfl)
    | step h3 h4 =>
      rw [h3.eq_loc WakeC0.step_z (fun _ _ _ _ _ h => by cases h) (fun _ h => by cases h)] at h4
      exact .inr (.inr h4)

/-- **`RunWf` at `wakeTh0`'s control**: its frame runs pass `cBodyW` to
`c0W` (`c0W_ctl`); neither it nor `cBodyW` is a load, store or buffer. -/
theorem runWf_th0 : RunWf wakeSrc cS [] := by
  have hc := WakeC0.c0W_ctl.2
  refine ⟨fun c' fs' hr x a e ty w ht hev => ?_, fun c' fs' hr x a τ e ht => ?_⟩
  · rcases frameRun_th0 hr with h | h | h
    · cases h; rw [cS_term] at ht; rcases ht with ht | ⟨_, ht⟩ <;> cases ht
    · cases h; rcases ht with ht | ⟨_, ht⟩ <;> cases ht
    · exact hc.cell c' fs' h x a e ty w ht hev
  · rcases frameRun_th0 hr with h | h | h
    · cases h; rw [cS_term] at ht; cases ht
    · cases h; cases ht
    · exact hc.zero c' fs' h x a τ e ht

/-- **`WS` at `wakeTh0`'s control from `WS` at `c0W`**, at a state whose
instruction is silent (`hd`): the machine's facts kept, `wakeTh0` placed
(`hpl`), no `ret`, no write (so the arena's and the counter's clauses are
vacuous), `runWf_th0`, and the abort sites' clauses (`c0W` neither an
overflow nor, the arena of at least two cells, a crossing box). -/
theorem ws_th0 {L : RuntimeLayout} {a : BitVec 64} {ar : Arena} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2}
    {lbl : Lbl} {lsize : Lsize} {frM : TermRun.Frame} {X0 : State → Prop} {s : State}
    (h : WS L a ar wakeSrc Dt Cl Ctx lbl lsize frM X0 s c0W) {s1 : State} (hd : isaLSE2.exec s = some (.done s1))
    (hpl : Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s cS []) (hcells : 2 ≤ ar.cells) :
    WS L a ar wakeSrc Dt Cl Ctx lbl lsize frM X0 s cS := by
  obtain ⟨hfs, hx, hst, hab, hac, hcl, -, -, -, -, -, habt⟩ := h
  have hnw : ∀ L, ¬ Spike.Lib.A64ConsumerA.WrAt s L := by
    rintro L (⟨_, _, _, he⟩ | ⟨_, _, _, he⟩) <;> exact nomatch hd.symm.trans he
  refine ⟨hfs, hx, hst, hab, hac, hcl, ?_, hpl, ?_, ?_, runWf_th0, ?_⟩
  · intro _ a h; rw [cS_term] at h; cases h
  · intro _ _ _ L hw _; exact (hnw L hw).elim
  · intro hw; exact (hnw _ hw).elim
  intro k a hk hpc
  obtain ⟨h1, h2⟩ := habt k a hk hpc
  refine ⟨?_, h2⟩
  rcases h1 with h | ⟨-, ⟨_, _, _, _, _, _, _, _, _, _, he, -⟩, -⟩ | ⟨-, hob⟩ | h
  · exact .inl h
  · rw [WakeC0.c0W_term] at he; cases he
  · rcases hob 0 fun _ => ⟨Nat.zero_le _, fun w hw => by cases hw⟩ with
      ⟨_, _, _, _, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, -, -, -, -, hlt⟩
    · rw [WakeC0.c0W_term] at he; cases he
    · omega
  · exact .inr (.inr (.inr h))

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (ls0 : Entry → Lsize) (Ctx : Entry → FragS isaLSE2) (frM : Entry → TermRun.Frame)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

set_option maxRecDepth 100000 in
/-- **`_start`'s `b scc_rt_start`**: silent, off a system call. -/
theorem start_cell (hprog : (Ly).prog = wakeProg) {s : State} (hs : s.exe = (Ly).exe)
    (hn : s.endPc = (Ly).endPc) (hpc : s.st.2 = (Ly).lab "_start") :
    ∃ s1, isaLSE2.exec s = some (.done s1) ∧ abi.atSys s = false := by
  have hL : Scc.Cert.Rt.A64.Lays (Ly).exe wakeProg (Ly).pfx := hprog ▸ (Ly).lays
  have hend : (Ly).endPc = Scc.Cert.Rt.A64.endOf (Ly).exe wakeProg (Ly).pfx := by rw [← hprog]
  have hcode := Spike.Lib.A64.Flow.code_of hL hend Spike.Lib.A64.WakePh.wake_rtCodeIn0.entry
    (q := (Ly).lab "_start") (Spike.Lib.A64.Flow.ofNat4_zero _)
  have hc := (hcode s hs hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  exact ⟨_, Kraken.Promising.Lower.A64.exec_b hc, Scc.Sem.A64.atSvc_false_of_cellAt hc (by intro _ h; cases h)⟩

/-- **`_start` is not the take site** (wake's label layout). -/
theorem start_ne_site (hlo : (Ly).Λ.code.lo = lo) (hpo : o.prog = wakeProg) :
    ((Ly).lab "_start").toBitVec.toNat ≠ ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have hlab : ∀ l x, Scc.Cert.Link.A64.codeOf lo wakeProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hp i l x (by rw [hlo, hpo]; exact h)
  exact Spike.Lib.A64.WakePh.WcW.site_ne_of_freeN hlab (Spike.Lib.A64.WakePh.WcW.freeAt_lab hlab (by wsfree_dec))

/-- **`wake_start_wc_h0W`'s exit at the root's memory side**: `wc_main`'s
heap abort call (`wX .abort`) in `wc_main`'s region, the pinned word kept. -/
def QabW (E : Entry) : Frag isaLSE2 := fun s c => ∃ v m0 σC,
  Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
    (wF (swR v (-384) 0) 336 (FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) 384 0#64 v) m0 σC)
    (wX (WakeRoot.msBot hp i ls0 Ctx E []) (Ly).lab (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC) .abort) s c ∧
  TP (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)) s

/-- **The level before the allocation at the start's marks** (`PhRec.μ`):
`W0` at the root's choices, `wc_heapAbStub`'s fragment; `W0W` at the
frames by `marks_target`. -/
abbrev W0S (E : Entry) : FragS isaLSE2 :=
  Spike.Lib.A64.WakeWf.W0 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) (ownG (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab))
    (Spike.Lib.WakeOD.arW hp i) wakeSrc DtW (Spike.Lib.A64.WriteAb.Ab (Ly).lab) (Spike.Lib.WakeOD.ClW hp i)
    (Spike.Lib.A64.ThreadsAb.Ac (Ly).lab Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM) (Ctx E) (L0T (Ly).Λ)
    (ls0T (ls0 E)) (frM E) (X0W (Ly) (Spike.Lib.WakeOSide.aW hp i E))

/-- **The take at `aW` is `PhRec.K` at `X0W`'s states**: `aW` is the take
site's label, the site's range there main's stack (`r0Of = rS0`), and no
`clone` refusal off the clone's pc. -/
theorem takeCKS_iff (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (E : Entry) {s s' : State}
    (hx : X0W (Ly) (Spike.Lib.WakeOSide.aW hp i E) s) :
    TakeCKS (Spike.Lib.WakeOSide.aW hp i E) (Spike.Lib.WakeOD.ClW hp i) s s' ↔
      Spike.Lib.A64.PhRec.K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) s s' := by
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hp i hpa hwp
  have hwpL : textProgram SccCertificate.asm = .ok (Ly).prog := by rw [hprog]; exact hwp
  have haW := Spike.Lib.WakeOSide.aW_site hp i hpa hwp hwpL (Spike.Lib.PlaceW.site_ofPlaceW hp i) E
  have hr0 : Spike.Lib.A64.Rt.Ti2.r0Of (Ly).lab = Spike.Lib.A64.Rt.rS0 (Ly) := by
    show (⟨(Spike.Lib.A64.Flow.Ret0.stacksA (_root_.Executable.labels (Ly).exe).label + 0#64).toNat, 16384⟩ :
      Scc.Sem.Range) = _
    rw [(Ly).lab_stacks]
  obtain ⟨hcl, hsr⟩ := hx
  constructor
  · rintro (⟨hpc, pm, rfl⟩ | ⟨⟨hc, -⟩, -⟩)
    · have hr := (hsr (by unfold pcOf; rw [hpc])).1
      exact ⟨hpc.trans haW, pm, by rw [hr, hr0]⟩
    · exact (hcl hc).elim
  · rintro ⟨hpc, pm, rfl⟩
    have hpa' : s.st.2 = Spike.Lib.WakeOSide.aW hp i E := hpc.trans haW.symm
    have hr := (hsr (by unfold pcOf; rw [hpa'])).1
    exact .inl ⟨hpa', pm, by rw [hr, hr0]⟩

set_option hygiene false in
/-- The start's fragment at the root's choices (`StartH0G`'s `WSW`). -/
local notation "WSE" => WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hp i) wakeSrc DtW
  (Spike.Lib.WakeOD.ClW hp i) (Ctx E) (L0T (Ly).Λ) (ls0T (ls0 E)) (frM E) (X0W (Ly) (Spike.Lib.WakeOSide.aW hp i E))

/-- **`RootOpen.hst0`** from `StartH0G.wake_start_wc_h0W`'s segment at the
root's choices (`hG`: inside `WS` under the take `PhRec.K`, from `_start`'s
node at `c0W`, at states with `Pe` given at the loaded thread (`hPe`), to
`wc_main`'s heap abort `QabW`), the heap abort's segment
(`hC`: from `QabW` at no frame to no exit, inside `W0W` under `TakeCKS` at
`msBot`), and `wakeTh0`'s placement at every state (`hplS`). The start pair
runs locally to `c0W` across `_start`'s silent branch (`SegW.prefix_done`,
`c0W_run`, `ws_th0`); the take at `aW = scc_rt_take_site` moves `X0W`'s
states as `PhRec.K` (the site's range main's stack `rS0`, no `clone`
refusal off the clone's pc); `WS` is `W0W` (`marks_target`); `liftS` at
the frames `[]`. -/
theorem hst0_of (E : Entry) (hE : E.Ok (Ly).Λ) (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = lo)
    (hplS : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ (L0T (Ly).Λ) s cS [])
    {Pe : State → Prop}
    (hPe : Pe (Scc.Sem.A64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)))
    (hG : SegW WSE (Spike.Lib.A64.PhRec.K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) wakeSrc (L0T (Ly).Λ)
      (WakeRoot.msBot hp i ls0 Ctx E [])
      (fun s c => Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (entryR E)
        (fun m => WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m) (entryN (Ly).lab c0W) s c ∧ Pe s)
      (QabW hp i ls0 Ctx E))
    (hC : SegWS (W0S hp i ls0 Ctx frM E) (Spike.Lib.A64.PhRec.K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) wakeSrc
      (L0T (Ly).Λ) (WakeRoot.msBot hp i ls0 Ctx E) ((QabW hp i ls0 Ctx E).at []) (fun _ _ _ => False)) :
    SegWS (W0W hp i E DtW (Ctx E) (ls0 E) (frM E)) (TakeCKS (Spike.Lib.WakeOSide.aW hp i E) (Spike.Lib.WakeOD.ClW hp i))
      wakeSrc (L0T (Ly).Λ) (WakeRoot.msBot hp i ls0 Ctx E) (WakeRoot.StartP hp i E) (fun _ _ _ => False) := by
  have hpo := Spike.Lib.A64.WakePh.StartPlaceLy.hp_W hpa hwp
  have hlo := Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hp i hpa hwp
  have hwpL : textProgram SccCertificate.asm = .ok (Ly).prog := by rw [hprog]; exact hwp
  have hne := start_ne_site hp i hlo hpo
  have hK : (WakeRoot.msBot hp i ls0 Ctx E []).K = some abi := rfl
  have hcells : 2 ≤ (Spike.Lib.WakeOD.arW hp i).cells :=
    show 2 ≤ Scc.Cert.PlaceOK.allocCells by decide
  -- D: the start pair runs locally into `hG`'s entry.
  have h1 : SegW WSE (Spike.Lib.A64.PhRec.K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) wakeSrc (L0T (Ly).Λ)
      (WakeRoot.msBot hp i ls0 Ctx E [])
      (fun s c => s = Scc.Sem.A64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata) ∧ c = cS)
      (QabW hp i ls0 Ctx E) := by
    refine hG.prefix_done fun s c' ⟨hs, hc⟩ => ?_
    subst hs hc
    have hA := Spike.Lib.LowerA64.entry_atW hp i c0W hE
    have hpc := Spike.Lib.LowerA64.hpc_ofPlaceW hp i E
    obtain ⟨s1, hd, hsy⟩ := start_cell hp i hprog hA.1 hA.2.1 hpc
    refine ⟨c0W, ⟨hA, hPe⟩, WakeC0.c0W_run.toLocalRun, rfl, ⟨s1, hd⟩,
      fun s' hk => hne (congrArg (fun x : Int64 => x.toBitVec.toNat) (hpc.symm.trans hk.1)),
      fun Ks hKs => ?_, fun hW => ws_th0 hW hd (hplS _) hcells⟩
    rw [hK] at hKs; cases hKs; exact hsy
  -- B: lift at the frames `[]`, the heap abort, the take at `aW` as `PhRec.K`, `W0S` as `W0W`.
  refine ((((Spike.Lib.SegWS.liftS (ms := WakeRoot.msBot hp i ls0 Ctx E) (W := W0S hp i ls0 Ctx frM E) []
    h1 fun _ _ h => h).seq hC).mono_K fun s c fs hW s' => takeCKS_iff hp i hpa hwp E hW.2.1).mono_W
    fun s c fs h => ?_).mono_pre fun s c fs ⟨hs, hc, hfs⟩ => ⟨⟨hs, hc⟩, hfs⟩
  unfold W0W; rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hwpL]; exact h

end Place

end Spike.Lib.A64.WakePh.StartH0B

/-- info: 'Spike.Lib.SegW.prefix_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.SegW.prefix_done

/-- info: 'Spike.Lib.LowerA64.entry_atW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.entry_atW

/-- info: 'Spike.Lib.A64.WakePh.StartH0B.ws_th0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartH0B.ws_th0

/-- info: 'Spike.Lib.A64.WakePh.StartH0B.start_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartH0B.start_cell

/-- info: 'Spike.Lib.A64.WakePh.StartH0B.hst0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartH0B.hst0_of
