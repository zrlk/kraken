/-
**The start pair in `h0`'s invariant from the start's segment** (wake.w,
x86-64; the twin of `Spike/Lib/A64WakeStartH0B.lean`'s `hst0_of` and its
pieces): the loaded thread with `wakeTh0`'s control at no frames is in
`X64WakeFinal.inv0G`, from a segment inside `WSX` under the take `PhRec.K`
at `msBotX`, from `_start`'s node at `c0W` to `wc_main`'s heap abort
(`StartH0X.wake_start_wc_h0X`'s shape), through `Land5.inv0_of_habW`.

- `out_prefix`, `segW_prefix` (generic): a row from `c` is one from `c'`
  when `c'` runs locally to `c` and the instruction is a silent tree (off a
  system call, no hold); a segment from `P` is one from the pairs whose
  control so runs into `P`.
- `localStepS_det`, `frameStep_eq_loc` (generic): a local step's successor
  is unique; a frame step of a control off a call and a `ret` is its local
  step.
- `cS`, `frameRun_th0`, `runWf_th0`: `wakeTh0`'s control, its frame runs
  (they pass `cBodyW` to `c0W`), `RunWf` there.
- `ws_th0`: `WSX` at `wakeTh0`'s control from `WSX` at `c0W` at a state
  whose instruction is a silent tree (`PlacedSE` there given, the arena's
  writes vacuous, `c0W` neither an overflow nor a crossing allocation).
- `hpc_ofPlaceWX`, `entry_atW`, `start_cell`, `start_ne_site`: the loaded
  thread at `_start`'s node at `ofPlaceWX` (`LowerX64.entry_atXEC`'s port),
  its `xorl %ebp, %ebp` silent and off a system call, off the take site.
- `hst0_of`: the start pair in `inv0G` from the segment (`hG`, its entry
  and exit carrying `U r1Of`), `wakeTh0`'s placement (`hplS`), and
  `Land5.inv0_of_habW`'s premises.
- `hst0_U`: `hst0_of` at the root's context, moved to `RootUL.CtxRU`
  (`RootUL.inv0_up`, `StartH0X.entry_U`).
- `hst0_W`: `hst0_U` with `hG` by `StartH0X.wake_start_wc_h0X`, its
  premises carried.

**Where x86-64 differs from AArch64**:
- the root is `X64WakeFinal`'s (`inv0G`, not `WakeRoot.RootOpen.hst0`):
  the conclusion is the start pair's membership (`OpenX.hinit`'s `I2 …
  inv0` at the loaded thread), not a `SegWS` from `StartP`;
- `_start`'s first instruction is `xorl %ebp, %ebp`, whose step is a
  silent tree (an undefined flag), so the prefix lemmas take a silent tree
  (`out_prefix`/`segW_prefix`; A64's `Out.prefix_done`/`SegW.prefix_done`
  take a `done`, `b scc_rt_start`);
- the level is `WSX` at `ownGXW` (A64 `WS` at `ownG`); `Land5`'s premises
  (`hbx`, `hc0`, `hpl0`, `HabLft`) are carried;
- the segment's entry and exit carry `U r1Of` (`wake_start_wc_h0X`'s), the
  entry's frame condition `Pz rS0` (`RootP.pz_rS0_load` at the loaded
  thread), its `U r1Of` by `entry_U` (needs `hA13`);
- the loader's facts are `cellsOf` parses and `outLit_prog` (A64
  `textProgram`); `LocalStepS.det`/`FrameStep.eq_loc` and the prefix
  lemmas are restated under new names (A64's live in its file).
-/
import Spike.Lib.X64WakeLand5
import Spike.Lib.X64WakeStartH0X
import Spike.Lib.X64WakeRootUL
import Spike.Lib.X64WakeC0
import Spike.Lib.X64WakeStartEWF

namespace Spike.Lib.X64.WakePh.StartH0B

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Lower (SilentTree)
open Scc.Sem (Entry)
open Scc.Sem.X64 (pcOf abi cellsOf codeLabel)
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.WakeWf (DtW RunWf X0W)
open Spike.Lib.X64.WakePh.StartH0 (C0Box)
open Spike.Lib.X64.KeepUn (U)
open Spike.Lib.X64.DmemPriv (WordsNoneP)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib (Arena FragS Frag SegW SegWS PlaceWX Ctl LocalRun LocalStepS FrameRun FrameStep Out MemSide)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64WakeT1 (wakeSrc)
open Spike.Lib.X64WakeParse (certAsm)
open Spike.Lib.X64WakeFinal (msBotX inv0G)
open Spike.Lib.X64.WakeC0 (c0W cBodyW)
open SccCertificate (outLit)

section Gen

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}

/-- **A silent row from a control `c` is one from any `c'` running locally
to `c`**: the instruction a silent tree (`hd`, `ht`) off a system call
(`hsys`), `c` holding nothing. -/
theorem out_prefix {X : Frag I} {s : I.State} {c c' : Ctl} (h : Out p lbl ms X s c) {t : EvTree I.State}
    {P0 : I.State → Prop} (hd : I.exec s = some t) (ht : SilentTree P0 t)
    (hsys : ∀ K, ms.K = some K → K.atSys s = false) (hr : LocalRun p c' c) (hc : c.hold = none) :
    Out p lbl ms X s c' := by
  cases h with
  | silent s' c'' he hr' hx => exact .silent s' c'' he (hr.trans hr') hx
  | choice P t he hs hx =>
    exact .choice P t he hs fun s' hp => let ⟨c'', hr', h⟩ := hx s' hp; ⟨c'', hr.trans hr', h⟩
  | load _ _ _ _ _ _ _ _ he => cases hd.symm.trans he; exact ht.elim
  | store _ _ _ _ _ _ _ _ _ _ _ _ he => cases hd.symm.trans he; exact ht.elim
  | rtStore _ _ _ _ _ he => cases hd.symm.trans he; exact ht.elim
  | rtLoad _ _ _ _ he => cases hd.symm.trans he; exact ht.elim
  | rtRmw _ _ _ _ _ he => cases hd.symm.trans he; exact ht.elim
  | sys K _ hK ha => rw [hsys K hK] at ha; cases ha
  | holdLoad _ _ _ _ _ _ _ _ he => cases hd.symm.trans he; exact ht.elim
  | xchgStore _ _ _ _ _ _ _ _ _ _ _ _ he => cases hd.symm.trans he; exact ht.elim
  | ctrRmw _ _ _ _ _ _ _ he => cases hd.symm.trans he; exact ht.elim
  | alloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh => rw [hc] at hh; cases hh
  | newStore _ _ _ _ _ _ _ _ _ _ _ _ he => cases hd.symm.trans he; exact ht.elim
  | emit K _ _ _ _ hK ha => rw [hsys K hK] at ha; cases ha
  | fence _ _ _ he => cases hd.symm.trans he; exact ht.elim

variable {W : Frag I} {K : I.State → I.State → Prop} {P P' Q : Frag I}

/-- **A segment from the pairs running locally into its entry**: each pair
`(s, c')` of `P'` has a `c` with `(s, c)` in `P`, `c'` running locally to
`c` (no hold), the instruction at `s` a silent tree, off a system call and
not moved from outside, and `W` moving from `(s, c)` to `(s, c')`. -/
theorem segW_prefix (h : SegW W K p lbl ms P Q)
    (hP : ∀ s c', P' s c' → ∃ c, P s c ∧ LocalRun p c' c ∧ c.hold = none ∧
      (∃ t P0, I.exec s = some t ∧ SilentTree P0 t) ∧ (∀ s', ¬ K s s') ∧
      (∀ Ks, ms.K = some Ks → Ks.atSys s = false) ∧ (W s c → W s c')) :
    SegW W K p lbl ms P' Q := by
  obtain ⟨inv, hs, hw, ho⟩ := h
  refine ⟨fun s c => inv s c ∨ P' s c, fun s c h => .inr h, ?_, ?_⟩
  · rintro s c (h | h)
    · exact hw s c h
    · obtain ⟨c0, hp0, -, -, -, -, -, hW⟩ := hP s c h
      exact hW (hw s c0 (hs s c0 hp0))
  · rintro s c (h | h)
    · exact Spike.Lib.kout_out_mono (ho s c h) fun s c h => h.imp_left .inl
    · obtain ⟨c0, hp0, hr, hh, ⟨t, P0, hd, ht⟩, hk, hsys, -⟩ := hP s c h
      exact ⟨fun _ => (out_prefix ((ho s c0 (hs s c0 hp0)).1 hk) hd ht hsys hr hh).mono
        fun s c h => h.imp_left .inl, Spike.Lib.KOut.none hk⟩

end Gen

/-- **A local step's successor is unique**. -/
theorem localStepS_det {p : Prog} {c c1 c2 : Ctl} (h1 : LocalStepS p c c1) (h2 : LocalStepS p c c2) :
    c1 = c2 := by
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
theorem frameStep_eq_loc {p : Prog} {c c1 : Ctl} {fs : List TermRun.Frame} {q : Ctl × List TermRun.Frame}
    (h : FrameStep p (c, fs) q) (hl : LocalStepS p c c1)
    (hc : ∀ x f is a e, c.term ≠ .let_ x (.call f is a []) e) (hr : ∀ a, c.term ≠ .ret a) : q = (c1, fs) := by
  cases h with
  | loc h' => rw [localStepS_det hl h']
  | call hc' => exact (hc _ _ _ _ _ hc').elim
  | ret hc' => exact (hr _ hc').elim

/-! ## `wakeTh0`'s control -/

/-- `wakeTh0`'s control (the start pair's). -/
abbrev cS : Ctl := Ctl.of Spike.Lib.X64WakePreAsm.wakeTh0

theorem cS_term : cS.term = .tail "main" [] (.var "me") := rfl

/-- **The frame runs from `wakeTh0`'s control** stop at it or at `cBodyW`,
or pass `c0W`. -/
theorem frameRun_th0 {q : Ctl × List TermRun.Frame} (h : FrameRun wakeSrc (cS, []) q) :
    q = (cS, []) ∨ q = (cBodyW, []) ∨ FrameRun wakeSrc (c0W, []) q := by
  cases h with
  | refl => exact .inl rfl
  | step h1 h2 =>
    rw [frameStep_eq_loc h1 Spike.Lib.X64.WakeC0.step_tail (fun _ _ _ _ _ h => by rw [cS_term] at h; cases h)
      (fun _ h => by rw [cS_term] at h; cases h)] at h2
    cases h2 with
    | refl => exact .inr (.inl rfl)
    | step h3 h4 =>
      rw [frameStep_eq_loc h3 Spike.Lib.X64.WakeC0.step_z (fun _ _ _ _ _ h => by cases h)
        (fun _ h => by cases h)] at h4
      exact .inr (.inr h4)

/-- **`RunWf` at `wakeTh0`'s control**: its frame runs pass `cBodyW` to
`c0W` (`c0W_ctl`); neither it nor `cBodyW` is a load, store or buffer. -/
theorem runWf_th0 : RunWf wakeSrc cS [] := by
  have hc := Spike.Lib.X64.WakeC0.c0W_ctl.2
  refine ⟨fun c' fs' hr x a e ty w ht hev => ?_, fun c' fs' hr x a τ e ht => ?_⟩
  · rcases frameRun_th0 hr with h | h | h
    · cases h; rw [cS_term] at ht; rcases ht with ht | ⟨_, ht⟩ <;> cases ht
    · cases h; rcases ht with ht | ⟨_, ht⟩ <;> cases ht
    · exact hc.cell c' fs' h x a e ty w ht hev
  · rcases frameRun_th0 hr with h | h | h
    · cases h; rw [cS_term] at ht; cases ht
    · cases h; cases ht
    · exact hc.zero c' fs' h x a τ e ht

/-- **`WSX` at `wakeTh0`'s control from `WSX` at `c0W`**, at a state whose
instruction is a silent tree (`hd`, `ht`): the machine's facts kept,
`wakeTh0` placed (`hpl`), no `ret`, no write (so the arena's and the
counter's clauses are vacuous), `runWf_th0`, and the abort sites' clauses
(`c0W` neither an overflow nor, the arena of at least two cells, a crossing
box). -/
theorem ws_th0 {L : RuntimeLayout} {a : BitVec 64} {ar : Arena} {Dt Cl : State → Prop} {Ctx : FragS isa}
    {lbl : Lbl} {lsize : Lsize} {frM : TermRun.Frame} {X0 : State → Prop} {s : State}
    (h : Spike.Lib.X64.WakePh.WSX L a ar wakeSrc Dt Cl Ctx lbl lsize frM X0 s c0W) {t : EvTree State}
    {P0 : State → Prop} (hd : isa.exec s = some t) (ht : SilentTree P0 t)
    (hpl : PlacedSE L.Λ lbl s cS []) (hcells : 2 ≤ ar.cells) :
    Spike.Lib.X64.WakePh.WSX L a ar wakeSrc Dt Cl Ctx lbl lsize frM X0 s cS := by
  obtain ⟨hfs, hx, hst, hab, hac, hcl, -, -, -, -, -, habt⟩ := h
  have hnw : ∀ L, ¬ Spike.Lib.X64ConsumerA.WrAt s L := by
    rintro L (⟨_, _, _, he⟩ | ⟨_, _, _, he⟩) <;> (cases hd.symm.trans he; exact ht.elim)
  refine ⟨hfs, hx, hst, hab, hac, hcl, ?_, hpl, ?_, ?_, runWf_th0, ?_⟩
  · intro _ a h; rw [cS_term] at h; cases h
  · intro _ _ _ L hw _; exact (hnw L hw).elim
  · intro hw; exact (hnw _ hw).elim
  intro k a hk hpc
  obtain ⟨h1, h2⟩ := habt k a hk hpc
  refine ⟨?_, h2⟩
  rcases h1 with h | ⟨-, ⟨_, _, _, _, _, _, _, _, _, _, he, -⟩, -⟩ | ⟨-, hob⟩ | h
  · exact .inl h
  · rw [Spike.Lib.X64.WakeC0.c0W_term] at he; cases he
  · rcases hob 0 fun _ => ⟨Nat.zero_le _, fun w hw => by cases hw⟩ with
      ⟨_, _, _, _, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, -, -, -, -, hlt⟩
    · rw [Spike.Lib.X64.WakeC0.c0W_term] at he; cases he
    · omega
  · exact .inr (.inr (.inr h))

/-! ## The loaded thread at `_start` (at `ofPlaceWX`) -/

section Entry

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
/-- The loaded thread at entry `E`. -/
local notation "S0" => Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)

/-- **The loaded thread is at `_start`** at `ofPlaceWX` (A1's `_start` at
the code base), at any entry state `E`. -/
theorem hpc_ofPlaceWX (E : Entry) : (S0).st.2 = (Ly).lab "_start" := by
  have hst : codeLabel (Ly).Λ.code.lo o.prog "_start" = some (Ly).Λ.code.lo := by
    have h1 := hpw.a1
    simp only [Scc.Cert.PlaceOK.X64.a1, Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.2
  haveI : Kraken.Executable.ValidLayout (S0).exe := (Ly).valid
  exact (Scc.Cert.Rt.X64.label_threadAt_of_codeLabel_below (E := E)
    (syms := Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)
    (by exact Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX_below hpw i hst) hst).symm

set_option maxRecDepth 100000 in
/-- **The loaded thread is at `_start`'s node with the control `c`** at
`ofPlaceWX` (`LowerX64.entry_atXEC`'s port): on the entry stack `entryR E`
of an admissible entry state, no word of the link loaded, the runtime's
words unloaded, and any `P` of the loaded memory (`hP`). -/
theorem entry_atW (c : Ctl) {E : Entry} (hE : E.Ok (Ly).Λ) {P : MachineData → Prop} (hP : P (S0).st.1) :
    At (Ly).exe (Ly).endPc (entryR E) (fun m => (WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m) ∧ P m)
      (Spike.Lib.X64.Rt.entryN0 (Ly).lab c) (S0) c := by
  refine ⟨rfl, Scc.Cert.Link.X64.endPc_threadAt_below _ _ _ _, rfl, hpc_ofPlaceWX hpw i E,
    ⟨{ rsp := UInt64.ofNat E.sp }, _, _, fun k =>
      BitVec.ofInt 64 ((Mem.loadInt E.stackMem ((entryR E).addr k) 8).getD 0)⟩,
    ⟨rfl, rfl, rfl, ?_, ?_⟩,
    ⟨⟨Spike.Lib.X64.DmemPriv.wordsNoneP_stackMem (Spike.Lib.PlaceWX.wf_link_of_placeWX i hpw) hE.1,
      Spike.Lib.X64.Rt.rtF_stackMem _ hE rfl⟩, hP⟩, rfl⟩
  · intro r k hr
    simp only [Spike.Lib.X64.Rt.entryN0, Spike.Lib.X64.SO.get] at hr
    split at hr
    · rename_i he
      subst he
      cases hr
      dsimp only
      show (UInt64.ofNat E.sp).toBitVec = BitVec.ofNat 64 E.sp + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl
    · simp [Spike.Lib.lk] at hr
  · intro k hk
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (Spike.Lib.X64.Rt.stack_wordE hE hk)
    refine ⟨j, hj, ?_⟩
    show _ = BitVec.ofInt 64 ((Mem.loadInt E.stackMem _ 8).getD 0)
    rw [hj]; rfl

/-- **`_start`'s `xorl %ebp, %ebp`**: a silent tree, off a system call. -/
theorem start_cell (hprog : (Ly).prog = wakeCells) {s : State} (hs : s.exe = (Ly).exe)
    (hn : s.endPc = (Ly).endPc) (hpc : s.st.2 = (Ly).lab "_start") :
    ∃ t P0, isa.exec s = some t ∧ SilentTree P0 t ∧ abi.atSys s = false := by
  haveI := (Ly).valid
  have hL : Scc.Cert.Rt.X64.Lays (Ly).exe wakeCells (Ly).pfx := hprog ▸ (Ly).lays
  have hend : (Ly).endPc = Scc.Cert.Rt.X64.endOf (Ly).exe wakeCells (Ly).pfx := by
    show Scc.Cert.Rt.X64.endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  have hs0 := Spike.Lib.X64.WakePh.wake_rtCodeIn0.start0
  simp only [Spike.Lib.X64.Rt.Code.Start.entryIn, Bool.and_eq_true] at hs0
  obtain ⟨⟨e0, -⟩, -⟩ := hs0
  have hcode := Scc.Cert.Rt.X64.code_field hL hend e0 (Spike.Lib.X64.Flow.ofNat_zero' _) s hs hn
  have hc := hcode.cell0 rfl rfl hpc
  obtain ⟨t, hex, hst⟩ := Spike.Lib.X64.exec_fi hc
  exact ⟨t, _, hex, hst, Scc.Sem.X64.atSyscall_false_of_cellAt hc (fun _ _ h => by cases h)⟩

/-- **A label's address moves with the base** (restated from
`X64.WakeSrcCtl.labelAddr_add`, not imported here). -/
theorem labelAddr_addB {D : Type} (lb : D → Option String) (sz : D → Nat) (l : String) :
    ∀ (ds : List D) (a b : Nat), Scc.Sem.labelAddr lb sz (a + b) l ds =
      (Scc.Sem.labelAddr lb sz b l ds).map (a + ·)
  | [], _, _ => rfl
  | d :: ds, a, b => by
    simp only [Scc.Sem.labelAddr]
    split
    · rfl
    · rw [Nat.add_assoc]; exact labelAddr_addB lb sz l ds a (b + sz d)

/-- `codeLabel` at a base is `codeLabel` at `0` moved by the base
(`X64.WakeSrcCtl.codeLabel_base`). -/
theorem codeLabel_baseB (b : Nat) (cells : List (Directive × Nat)) (l : String) :
    codeLabel b cells l = (codeLabel 0 cells l).map (b + ·) := by
  unfold codeLabel
  simpa using labelAddr_addB (fun c : Directive × Nat => Scc.Sem.X64.labelName c.1) (·.2) l cells b 0

/-- **`_start` is not the take site** (wake's label layout: `_start` at the
code base `lo`, the site `1877` bytes past it; stated relative to `lo`, so
independent of the base's value). -/
theorem start_ne_site (hlo : (Ly).Λ.code.lo = Spike.Lib.X64.WakePh.lo) (hpo : o.prog = wakeCells) :
    ((Ly).lab "_start").toBitVec.toNat ≠ ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have hlab : ∀ l x, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw i l x (by rw [hlo, hpo]; exact h)
  have h0 : codeLabel 0 wakeCells "_start" = some 0 := by rw [← codeT_eq]; decide +kernel
  have hs1 : codeLabel 0 wakeCells Spike.Lib.X64.Flow.Ret0.StackTake.siteL = some 1877 := by
    rw [← codeT_eq]; decide +kernel
  have e1 : (Ly).lab "_start" = Int64.ofNat (Spike.Lib.X64.WakePh.lo + 0) :=
    hlab _ _ (by rw [codeLabel_baseB, h0]; rfl)
  have e2 : (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat (Spike.Lib.X64.WakePh.lo + 1877) :=
    hlab _ _ (by rw [codeLabel_baseB, hs1]; rfl)
  rw [e1, e2]; decide

end Entry

/-! ## The start pair in `inv0G` -/

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 outLit) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (cT : Entry → Loc) (ls0 : Entry → Lsize) (Ctx : Entry → FragS isa) (frM : Entry → TermRun.Frame)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The loaded thread at entry `E`. -/
local notation "S0" =>
  Scc.Sem.X64.threadAt E (Ly).Λ.code.lo outLit.prog (Scc.Sem.loadSyms (Ly).Λ outLit.secs.rodata)

set_option hygiene false in
/-- The start's level at `ownGXW` at entry `E`. -/
local notation "WSE" => Spike.Lib.X64.WakePh.WSX (Ly) (ntA (Ly).lab) (Spike.Lib.X64.WakeOD.arW hp i) wakeSrc DtW
  (Spike.Lib.X64.WakeOD.ClW hp i) (Ctx E) (L0T (Ly).Λ) (ls0T (ls0 E)) (frM E)
  (X0W (Ly) (Spike.Lib.X64WakeOSide.aW hp i E))

/-- **The start pair is in `inv0G`** at the frames `[]`, from the start's
segment `hG` (inside `WSX` under the take `PhRec.K`, from `_start`'s node
at `c0W` with `Pz rS0` and `U r1Of`, to `wc_main`'s heap abort `QabX` with
`U r1Of`): the start pair runs locally to `c0W` across `_start`'s silent
`xorl` (`segW_prefix`, `c0W_run`, `ws_th0`), then `Land5.inv0_of_habW`. -/
theorem hst0_of (E : Entry) (hE : E.Ok (Ly).Λ) (hpa : cellsOf certAsm = some outLit.prog)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ outLit.prog outLit.secs = true)
    /- `c0W`'s placement, `wakeTh0`'s placement, the heap abort path's lift -/
    (hpl0 : ∀ s, PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0W [])
    (hplS : ∀ s, PlacedSE (Ly).Λ (L0T (Ly).Λ) s cS [])
    (hlft : Spike.Lib.X64.WakePh.StartH0C.HabLft (Ly))
    (hG : SegW (WSE) (Spike.Lib.X64.PhRec.K (Ly) (RS0)) wakeSrc (L0T (Ly).Λ) (msBotX hp i cT ls0 Ctx frM E [])
      (fun s c => At (Ly).exe (Ly).endPc (entryR E)
        (fun m => (WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m) ∧ Spike.Lib.X64Consumer.Pz (RS0) m)
        (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0W) s c ∧ U R1 s)
      (fun s c => Spike.Lib.X64.WakePh.Land5.QabX hp i cT ls0 Ctx frM c0W E s c ∧ U R1 s)) :
    inv0G hp i cT ls0 Ctx frM E (S0) cS [] := by
  have hpo : outLit.prog = wakeCells := Spike.Lib.X64WakeParse.outLit_prog
  have hne := start_ne_site hp i hlo hpo
  have hK : (msBotX hp i cT ls0 Ctx frM E []).K = some abi := rfl
  have hcells : 2 ≤ (Spike.Lib.X64.WakeOD.arW hp i).cells :=
    show 2 ≤ Scc.Cert.PlaceOK.allocCells by decide
  have h1 : SegW (WSE) (Spike.Lib.X64.PhRec.K (Ly) (RS0)) wakeSrc (L0T (Ly).Λ) (msBotX hp i cT ls0 Ctx frM E [])
      (fun s c => s = S0 ∧ c = cS) (Spike.Lib.X64.WakePh.Land5.QabX hp i cT ls0 Ctx frM c0W E) := by
    refine segW_prefix (hG.mono_post fun _ _ h => h.1) fun s c' ⟨hs, hc⟩ => ?_
    subst hs hc
    have hA := entry_atW hp i c0W hE (P := Spike.Lib.X64Consumer.Pz (RS0))
      (Spike.Lib.X64.WakePh.RootP.pz_rS0_load hE.1 _ _ _)
    have hpc := hpc_ofPlaceWX hp i E
    obtain ⟨t, P0, hd, ht, hsy⟩ := start_cell hp i hpo hA.1 hA.2.1 hpc
    refine ⟨c0W, ⟨hA, Spike.Lib.X64.WakePh.StartH0X.entry_U hp i hE.1 hA13 _ _⟩,
      Spike.Lib.X64.WakeC0.c0W_run.toLocalRun, rfl, ⟨t, P0, hd, ht⟩,
      fun s' hk => hne (congrArg (fun x : Int64 => x.toBitVec.toNat) (hpc.symm.trans hk.1)),
      fun Ks hKs => ?_, fun hW => ws_th0 hW hd ht (hplS _) hcells⟩
    rw [hK] at hKs; cases hKs; exact hsy
  exact Spike.Lib.X64.WakePh.Land5.inv0_of_habW hp i cT ls0 Ctx frM E hpa hlo Spike.Lib.X64.WakeC0.c0W_box
    Spike.Lib.X64.WakeC0.c0W_ctl hpl0 hlft h1 _ _ ⟨rfl, rfl⟩

set_option hygiene false in
/-- The root's context at `c0W`. -/
local notation "CtxL" => fun E : Entry =>
  Spike.Lib.X64.WakePh.Land.CtxR (Ly) c0W (Spike.Lib.X64.WakePh.Land.refW certAsm hp i ls0 E)

set_option hygiene false in
/-- The root's `cT`: the dummy heap word. -/
local notation "cTR" => fun _ : Entry => Spike.Lib.X64WakeHG.cTW hp i

/-- **The start pair is in `inv0G` at `CtxRU`**: `hst0_of` at the root's
context `CtxR` at `c0W`, moved by `RootUL.inv0_up` with `U r1Of` at the
loaded thread (`StartH0X.entry_U`). -/
theorem hst0_U (E : Entry) (hE : E.Ok (Ly).Λ) (hpa : cellsOf certAsm = some outLit.prog)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ outLit.prog outLit.secs = true)
    (hpl0 : ∀ s, PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0W [])
    (hplS : ∀ s, PlacedSE (Ly).Λ (L0T (Ly).Λ) s cS [])
    (hlft : Spike.Lib.X64.WakePh.StartH0C.HabLft (Ly))
    (hG : SegW (Spike.Lib.X64.WakePh.WSX (Ly) (ntA (Ly).lab) (Spike.Lib.X64.WakeOD.arW hp i) wakeSrc DtW
        (Spike.Lib.X64.WakeOD.ClW hp i) ((CtxL) E) (L0T (Ly).Λ) (ls0T (ls0 E)) (frM E)
        (X0W (Ly) (Spike.Lib.X64WakeOSide.aW hp i E)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) wakeSrc (L0T (Ly).Λ) (msBotX hp i cT ls0 (CtxL) frM E [])
      (fun s c => At (Ly).exe (Ly).endPc (entryR E)
        (fun m => (WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m) ∧ Spike.Lib.X64Consumer.Pz (RS0) m)
        (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0W) s c ∧ U R1 s)
      (fun s c => Spike.Lib.X64.WakePh.Land5.QabX hp i cT ls0 (CtxL) frM c0W E s c ∧ U R1 s)) :
    inv0G hp i cT ls0 (Spike.Lib.X64.WakePh.RootUL.CtxRU hp i c0W ls0) frM E (S0) cS [] :=
  Spike.Lib.X64.WakePh.RootUL.inv0_up hp i c0W ls0 frM cT E _ _ _
    (hst0_of hp i cT ls0 (CtxL) frM E hE hpa hlo hA13 hpl0 hplS hlft hG)
    (Spike.Lib.X64.WakePh.StartH0X.entry_U hp i hE.1 hA13 _ _)

/-- **The start pair is in `inv0G` at `CtxRU`, from the start's
segment**: `hst0_U` at `cT := cTW` with `hG` by
`StartH0X.wake_start_wc_h0X` (at `inv0 := ⊥`, `inv1 := inv1W`, `msBotX`'s
fragment), its premises carried: the instance facts (`hstat`, `hpin2`,
`hctrD`, `hc`), `c0W`'s placement and code facts (`hpl0`, `hC0`), `h1`'s
`Box ⊆ inv1W` clause (`hB1`) and `wc_main`'s frame inside `F0` (`hF0`). -/
theorem hst0_W (E : Entry) (hE : E.Ok (Ly).Λ) (hpa : cellsOf certAsm = some outLit.prog)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ outLit.prog outLit.secs = true)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hctrD : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], (Ly).Λ.data.contains a.toNat)
    (hc : Spike.Lib.X64.Rt.CtrZ outLit) {lbl' : Lbl} {F0 : MachineData → Prop}
    (hpl0 : ∀ s, PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0W [])
    (hC0 : Spike.Lib.X64Consumer.CFacts (Ly).Λ lbl' c0W)
    (hplS : ∀ s, PlacedSE (Ly).Λ (L0T (Ly).Λ) s cS [])
    (hlft : Spike.Lib.X64.WakePh.StartH0C.HabLft (Ly))
    (hB1 : ∀ l b n, L0T (Ly).Λ l = none →
      Spike.Lib.HeapLand.AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n →
      ∀ s c, Spike.Lib.X64.Flow.WakeWc.Box (Ly) (msBotX hp i (cTR) ls0 (CtxL) frM E []) F0 l b n s c →
        Spike.Lib.X64.WakeH1Inv.inv1W certAsm hp i E (Spike.Lib.X64WakeHG.cTW hp i) DtW ((CtxL) E) (ls0 E)
          l b n s c [])
    (hF0 : ∀ v m0 σC m, Spike.Lib.X64.Flow.WakeM.wF (Spike.Lib.X64.WakePh.MainGlue.RS
        Spike.Lib.X64.WakePh.StartFacts.wcLsw v) Spike.Lib.X64.WakePh.StartFacts.wcD
      (Spike.Lib.X64.WakePh.MainGlue.FS (Ly) (RS0) Spike.Lib.X64.WakePh.StartFacts.wcLsw 0#64 v) m0 σC m → F0 m) :
    inv0G hp i (cTR) ls0 (Spike.Lib.X64.WakePh.RootUL.CtxRU hp i c0W ls0) frM E (S0) cS [] := by
  have hax : (Spike.Lib.X64WakeOSide.aW hp i E).toBitVec.toNat =
      ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
    rw [Spike.Lib.X64WakeOSide.aW_site hp i hpa E]
  exact hst0_U hp i (cTR) ls0 frM E hE hpa hlo hA13 hpl0 hplS hlft
    (Spike.Lib.X64.WakePh.StartH0X.wake_start_wc_h0X certAsm hp i ls0 hE (Dt := DtW) (frM := frM E)
      (inv0 := fun _ _ _ => False)
      (inv1 := Spike.Lib.X64.WakeH1Inv.inv1W certAsm hp i E (Spike.Lib.X64WakeHG.cTW hp i) DtW ((CtxL) E) (ls0 E))
      Spike.Lib.X64WakeParse.outLit_prog hlo hstat hA13 hpin2 hctrD hc hax hpl0 hC0 hB1 hF0)

end Place

end Spike.Lib.X64.WakePh.StartH0B

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.out_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.out_prefix

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.segW_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.segW_prefix

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.localStepS_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.localStepS_det

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.frameStep_eq_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.frameStep_eq_loc

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.frameRun_th0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.frameRun_th0

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.runWf_th0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.runWf_th0

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.ws_th0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.ws_th0

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.hpc_ofPlaceWX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.hpc_ofPlaceWX

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.entry_atW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.entry_atW

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.start_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.start_cell

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.labelAddr_addB' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.labelAddr_addB

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.codeLabel_baseB' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.codeLabel_baseB

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.start_ne_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.start_ne_site

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.hst0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.hst0_of

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.hst0_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.hst0_U

/-- info: 'Spike.Lib.X64.WakePh.StartH0B.hst0_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0B.hst0_W
