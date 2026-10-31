/-
**`hB_box`'s `hmid`** (x86-64, the twin of `Spike/Lib/A64WakeHMid.lean`;
`X64.WakeBoxW.hB_box`): wake's box, past its store, runs inside `h1`'s fence
`W1X` under `h1`'s outside move `K1W` to main's `clone` (`CloneP`), at the
fresh label `l` of `n` bytes at `b`.

`wake_wc_mid_hatW` from the box's landing `bX`, its source facts `QB` (the
box's), its fence off the clone's and the take site's pcs (`wcMidW_offC`)
and `W1W`'s (`wcMidW_w1`), inside `NoSetFsW` (`WcMidW.noSetFs`), at no
outside move; `K1W` moves no state of the fence (`takeCKS_none`,
`SegW.mono_K`); lifted at no frames (`SegWS.liftS`, `X1W` off both pcs by
`x1W_off`); the pair `p = (c, me)` taken after the segment (`pub_spawn`,
`SegWS.post_run`).

- `at_bX_ms`: the landing across memory sides admitting the same box calls.
- `BoxPure`: `Box`'s facts of its ghosts alone (`R`, `F`, `J0`, `t`, `n`).
- `QB`: the box's source facts at `l`, `b`.
- `pub_spawn`: from the box's published control (`boxPubCtl`) the pair's
  local step to `SpawnSrc l`.
- `at_wcNS_ctl`, `at_JS_ctl`: the clone's node and main's parent node at
  any control (their invariants pin the control to their parameter).
- `WB`: the fence `wake_wc_mid_hatW` runs in.
- `HMidP`: the named premises at one ghost: `wcWf`, `res`, `tcb`
  (`wcMidW_w1`'s), `resA`, `hdrA`, `tcbA`, `tid`, `ti`
  (`wake_wc_mid_hatW`'s at no outside move), and `wcl` (`W1W` at the clone's
  `syscall`).
- `hmid_box`: `hmid` at `l`, `b`, `n`.

**Unlike AArch64**:
- x86-64's `wake_wc_mid_hatW` has no source parameter `S`: its exit is at
  the box's published control `boxPubCtl c0 ty l` (the `mfence`'s
  publication inside the segment), so the pair step to `spawnTerm`
  (`SpawnSrc l`) is taken after the segment as a pending frame run
  (`pub_spawn`, `SegWS.post_run`), and `wcNS`/`JS` are moved to the new
  control (`at_wcNS_ctl`, `at_JS_ctl`); there is no `SB`.
- The fence is inside `NoSetFsW` (`WcMidW.noSetFs`, x86-64's thread pointer
  kept by no `arch_prctl`), not `NoMsrW`.
- The assembly is a parameter `asm` (`W1W`, `W1X`, `CloneP`, `ms1W`); the end
  of text is `X64WakeH1Inv.endR`; the layout's program is `wakeCells`.
- The regions: `Box`'s `R.lo ≤ -320`, `16 ≤ R.hi` (no `hfit`/`hup`), the
  callees at `-72` (`rAR R`, `R.callee (-72) (-184) 8`,
  `R.callee (-72) (-248) 8`), `Abs R oC` in `ti`; `CloneP`'s last conjunct
  (the caller's `%rsp`) from `Box`'s `%rsp` conjunct.

No absolute address appears in this file.
-/
import Spike.Lib.X64WakeBoxW
import Spike.Lib.X64WakeWcW1
import Spike.Lib.X64WakeWcHat
import Spike.Lib.X64WakeWcNoMsr
import Spike.Lib.X64WakeAWSite

namespace Spike.Lib.X64.WakeHMid

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.WakeWc (WcMainW WcMidW bX t2 kOf rAR wcMidW_w1 MidG FrG FrMG)
open Spike.Lib.X64.WakePh.WcSp4 (wcNI)
open Spike.Lib.X64.WakePh.WcClone (oW wcNS)
open Spike.Lib.X64.WakePh.Tcb2Call (oC tcb2Q)
open Spike.Lib.X64.Flow.Ret0 (tiN tiX StOk CallerCells)
open Spike.Lib.X64.Rt (TcbOkGA hdrA TcbWG)
open Spike.Lib.X64.Rt.Reserve (ResOkA ReserveW)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.WakePh.Parent (JS)
open Spike.Lib.X64WakePreA (cloneAt)
open Spike.Lib.X64WakeBoxDefs (boxTerm boxPubCtl)
open Spike.Lib.X64WakeLoadT (L0T tcb0)
open Spike.Lib.X64.WakeOPremW (W1W)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Spike.Lib.X64.WakeBoxW (SpawnSrc W1X CloneP)
open SccCode (wakeCells)
open Scc.Cert.Rt.X64 (Lays endOf)

/-- **The landing across memory sides** admitting the same box calls, with
the same arena geometry (`heap`, `cells`, `off`, `units`). -/
theorem at_bX_ms {ms ms' : MemSide isa} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Ctl}
    (hq : ∀ q : Spike.Lib.X64.Alloc.Call, q.OKB ms (_root_.Executable.labels exe).label →
      q.OKB ms' (_root_.Executable.labels exe).label)
    (hg : ms'.heap = ms.heap ∧ ms'.cells = ms.cells ∧ ms'.off = ms.off ∧ ms'.units = ms.units)
    (h : At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c) :
    At exe endPc R F (bX ms' (_root_.Executable.labels exe).label J0 l A) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := hg
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, hq _ q.2⟩, h1, h2, h3, by rw [g1, g2, g3, g4]; exact h4⟩

/-- **`Box`'s facts of its ghosts alone**: the region `R`, the frame
condition `F`, the entry node `J0`, the thread pointer `t`, one object. -/
def BoxPure (L : Spike.Lib.X64.Rt.RuntimeLayout) (F0 : MachineData → Prop) (n : Nat) (R : Region)
    (F : MachineData → Prop) (J0 : AS → Ctl → Prop) (t : UInt64) : Prop :=
  (R.OK ∧ R.base.toNat % 16 = 0 ∧ FStable R F ∧ R.lo ≤ -320 ∧ 16 ≤ R.hi) ∧
    (∀ k, -80 ≤ k → k ≤ -72 → L.Λ.stackPool.lo < (R.addr k).toNat ∧
      (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size) ∧
    (∀ m, F m → F0 m) ∧
    ((∃ (J : AS → Ctl → Prop) (σC : AS), J0 = WakeM.wJ0 (WakeM.wNC (_root_.Executable.labels L.exe).label J).J σC) ∧
      (∀ σe c, J0 σe c → σe.regs.rdi.toNat = tcb0 L.Λ) ∧ R.base.toNat + 64 = L.stacksA.toNat + 16384 ∧
      ∀ σe c, J0 σe c → σe.regs.get64 .rsp = R.base + 8#64) ∧
    t.toNat = L.pinA.toNat + 8 ∧ n = 1 ∧
    ((∀ m pm, F m → F (Ret0.takeMem pm (Spike.Lib.X64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label) m)) ∧
      (∀ m m' : MachineData, m'.dmem = m.dmem → F m → F m') ∧ R.hi ≤ 64 ∧
      (∀ m, F m → Ret0.StackOff (Spike.Lib.X64.Rt.Ti2.r0Of (_root_.Executable.labels L.exe).label) R m) ∧
      R.lo % 8 = 0 ∧ R.hi % 8 = 0)

/-- **The box's source facts** at `l` (`b`): `boxTerm`, no hold, `o` at `l`'s
owned locative, `me` at main's. -/
def QB (l : WeakMem.AllocLabel) (b : Nat) (l' : WeakMem.AllocLabel) (A : Nat) (c : Ctl) : Prop :=
  l' = l ∧ A = b ∧ c.term = boxTerm ∧ c.hold = none ∧
    TermRun.evalAt c.env (.var "o") = some (.ptr .own .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
    TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])

/-- **The pair after the publication**: at the box's published control
(`boxPubCtl`, `c` bound to `l`'s public locative) with `me` main's, the
pair `p = (c, me)` is one local step to `SpawnSrc l`. -/
theorem pub_spawn {p : Prog} {c0 : Ctl} {l : WeakMem.AllocLabel}
    (hme : TermRun.evalAt c0.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])) :
    ∃ c', FrameRun p (boxPubCtl c0 .int l, []) (c', []) ∧ SpawnSrc l c' := by
  have hc : TermRun.evalAt (boxPubCtl c0 .int l).env (.var "c") =
      some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) := by
    simp [boxPubCtl, TermRun.evalAt, TermRun.lookupE]
  have hm : TermRun.evalAt (boxPubCtl c0 .int l).env (.var "me") =
      some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) := by
    simpa [boxPubCtl, TermRun.evalAt, TermRun.lookupE] using hme
  refine ⟨_, .single (.loc (LocalStep.toS (Spike.Lib.Form.localStep_pair rfl hc hm))), rfl, rfl, ?_, ?_, ?_⟩
  all_goals simp [TermRun.evalAt, TermRun.lookupE, boxPubCtl] at hm ⊢
  all_goals exact hm

/-- **The post-pair control is inhabited** (non-vacuity of `pub_spawn`'s
exit): from a box control binding only `me` to main's id, the pair reaches
a control at `SpawnSrc l`. -/
example (p : Prog) (l : WeakMem.AllocLabel) : ∃ c', FrameRun p
    (boxPubCtl ⟨boxTerm, [("me", .tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])], none⟩ .int l, []) (c', []) ∧
    SpawnSrc l c' :=
  pub_spawn (by simp [TermRun.evalAt, TermRun.lookupE])

/-- **The clone's node at any control**: `wcNS`'s invariant pins the
control to its parameter, and nothing else reads it. -/
theorem at_wcNS_ctl {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {lab : Label → Int64} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} {s : State} {c c' : Ctl}
    (h : At exe endPc R F (wcNS lab c t k cA m fr) s c) : At exe endPc R F (wcNS lab c' t k cA m fr) s c' := by
  obtain ⟨he, hn, hd, hpc, σ, hA, hF, ⟨⟨-, hJA⟩, hL⟩, hr⟩ := h
  exact ⟨he, hn, hd, hpc, σ, hA, hF, ⟨⟨rfl, hJA⟩, hL⟩, hr⟩

/-- **Main's parent node at any control**: `JS` pins the control to its
parameter. -/
theorem at_JS_ctl {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {pc : Int64}
    {cA fp ra tp : BitVec 64} {s : State} {c c' : Ctl}
    (h : At exe endPc R F ⟨pc, oW, JS c cA fp ra tp⟩ s c) : At exe endPc R F ⟨pc, oW, JS c' cA fp ra tp⟩ s c' := by
  obtain ⟨he, hn, hd, hpc, σ, hA, hF, -, hr⟩ := h
  exact ⟨he, hn, hd, hpc, σ, hA, hF, rfl, hr⟩

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Spike.Lib.X64Consumer.Lsize)
  (l : WeakMem.AllocLabel) (b n : Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- `h1`'s memory side at no frames. -/
local notation "ms1" => WakeH1Inv.ms1W asm hp i E cT ls0 l b n []

set_option hygiene false in
/-- The end of text. -/
local notation "eR" => WakeH1Inv.endR hp i

/-- **The fence `wake_wc_mid_hatW` runs in**: `W1W` at no frames, off the
clone's pc and the take site's. -/
def WB : Frag isa := fun s c => W1W asm hp i E Dt Ctx ls0 l b n s c [] ∧
  pcOf s ≠ WakeWc.clonePc (Ly) ∧ pcOf s ≠ ((Ly).lab Ret0.StackTake.siteL).toBitVec.toNat

/-- **`hmid`'s named premises at one ghost** (`R`, `F`, `J0`, `t`). -/
structure HMidP (R : Region) (F : MachineData → Prop) (J0 : AS → Ctl → Prop) (t : UInt64) : Prop where
  /-- `wc_main`'s nodes inside `W1W`. -/
  wcWf : WcMainW (fun s c => W1W asm hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe eR R F F
    (tpXa ms1 t) J0 (QB l b)
  /-- The reserve's nodes inside `W1W`. -/
  res : ∀ g : Ret0.AllocTcb.G × Ctl, g.1.ra = ((Ly).lab ".Lwc_main.x19").toBitVec →
    ∀ nd, ReserveW (fun s c => W1W asm hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe eR (rAR R)
      (fun m => F m ∧ CallerCells R (-72) (-40) 8 m ∧ WakeWc.ResCtx (Ly).lab R
        (WakeWc.rN (tpXa ms1 t) (Ly).lab R J0 (QB l b) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- The second TCB's nodes inside `W1W`. -/
  tcb : ∀ c0 cA m fr, MidG (QB l b) c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    ∀ g : Ret0.AllocTcb.G, g.ra = ((Ly).lab ".Lwc_main.x20").toBitVec →
    ∀ nd, TcbWG (fun s c => W1W asm hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe eR
      (R.callee (-72) (-184) 8) (fun mm => F mm ∧ CallerCells R (-72) (-184) 8 mm ∧
        WakeWc.TcbCtx (Ly).lab R (WakeWc.wcNCR (Ly).lab c0 cA m fr).J c0 g mm) (tcb2Q g c0) nd
  /-- `wake_wc_mid_hatW`'s `hres`. -/
  resA : ∀ g : Ret0.AllocTcb.G × Ctl, ResOkA ms1 F (Ly).exe eR (rAR R) F ⟨g.1, 0#64, g.2⟩
  /-- `wake_wc_mid_hatW`'s `hhdr`. -/
  hdrA : ∀ c0 g, StOk ms1 F (hdrA (Ly).lab (tcb2Q g c0)) ((tcb2Q g c0).h ||| 1#64 <<< 36)
  /-- `wake_wc_mid_hatW`'s `htcb`. -/
  tcbA : ∀ c0 g, TcbOkGA ms1 F (Ly).exe eR (R.callee (-72) (-184) 8) F (tcb2Q g c0)
  /-- `wake_wc_mid_hatW`'s `htid`. -/
  tid : (ms1).rt (t2 (Ly).lab + 56#64).toNat ∧ (ms1).mp ⟨t2 (Ly).lab + 56#64, 8⟩ true ∧
    (ms1).G ⟨t2 (Ly).lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (t2 (Ly).lab + 56#64) 8 = none
  /-- `wake_wc_mid_hatW`'s `hti`, inside `WB`, at no outside move, no post
  beyond the frame. -/
  ti : ∀ (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) (R' : Region) (F' : MachineData → Prop),
    R'.OK → R'.lo ≤ -248 → 8 ≤ R'.hi →
    FStable R' F' → KStable (fun _ _ => False) F' → (∀ m, F' m → F m) → R' = R.callee (-72) (-248) 8 →
    (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -72) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
    ∀ g : Ret0.AllocTcb.G,
      (∃ σC c, (wcNI (Ly).lab c0 (t2 (Ly).lab) cA m fr).J σC c ∧
        (tiN (Ly).lab (WakeWc.tiQ (t2 (Ly).lab) c0 g) .e).J (enter (-72) σC) c) →
      (∀ m', F' m' → ∃ mC σC c, Abs R oC mC σC ∧ (wcNI (Ly).lab c0 (t2 (Ly).lab) cA m fr).J σC c ∧
        (tiN (Ly).lab (WakeWc.tiQ (t2 (Ly).lab) c0 g) .e).J (enter (-72) σC) c ∧
        ∀ k, R.Off k → ¬ R'.Off (k - -72) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      SegW (NoSetFsW (WB asm hp i E Dt Ctx ls0 l b n) (fun _ _ => False)) (fun _ _ => False) X64WakeT1.wakeSrc
        (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b) (tpXa ms1 t)
        (At (Ly).exe eR R' F' (tiN (Ly).lab (WakeWc.tiQ (t2 (Ly).lab) c0 g) .e))
        (fun s c => ∃ x, At (Ly).exe eR R' F' (tiX (Ly).lab (WakeWc.tiQ (t2 (Ly).lab) c0 g) x) s c ∧ True)
  /-- `W1W` at the clone's `syscall`, and the child's stack in private
  memory there (`scc_rt_thread_init`'s take). -/
  wcl : ∀ s c cA m fr,
    At (Ly).exe eR R F (wcNS (Ly).lab c (t2 (Ly).lab) (kOf (Ly).lab) cA m fr) s c →
    SpawnSrc l c → W1W asm hp i E Dt Ctx ls0 l b n s c [] ∧ Ret0.StackM (X64WakeOSide.r1W hp i) s.st.1

/-- **`hB_box`'s `hmid` at `l`, `b`, `n`**: from the box past its store to
main's clone inside `W1X` under `K1W`, given the layout's program wake's
(`hprog`), the take site at `scc_rt_take_site` (`haW`: `aW_site`), the box
call's premises from `ms0` at `h1`'s side (`hokb`: `okb_ms1`), `ms0`'s
arena geometry the arena's (`hg`, for the landing's allocator fact), and
`HMidP` at every ghost of `Box`'s. -/
theorem hmid_box {ms0 : MemSide isa} {F0 : MachineData → Prop} (hprog : (Ly).prog = wakeCells)
    (haW : X64WakeOSide.aW hp i E = (Ly).lab Ret0.StackTake.siteL)
    (hokb : ∀ q : Spike.Lib.X64.Alloc.Call, q.OKB ms0 (Ly).lab → q.OKB ms1 (Ly).lab)
    (hg : ms0.heap = (WakeOD.arW hp i).heap ∧ ms0.cells = (WakeOD.arW hp i).cells ∧
      ms0.off = (WakeOD.arW hp i).off ∧ ms0.units = (WakeOD.arW hp i).units)
    (hP : ∀ R F J0 t, BoxPure (Ly) F0 n R F J0 t → HMidP asm hp i E cT Dt Ctx ls0 l b n R F J0 t) :
    SegWS (W1X asm hp i E Dt Ctx ls0 l b n) (WakeH1Inv.K1W hp i E) X64WakeT1.wakeSrc
      (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
      (WakeH1Inv.ms1W asm hp i E cT ls0 l b n) (fun s c fs => WakeWc.Box (Ly) ms0 F0 l b n s c ∧ fs = [])
      (CloneP asm hp i E Dt Ctx ls0 l b n) := by
  have hL : Lays (Ly).exe wakeCells (Ly).pfx := hprog ▸ (Ly).lays
  have hE : (Ly).endPc = eR := by
    show endOf _ (Ly).prog _ = _; rw [hprog]
  refine (SegWS.exists_pre (P := fun (g : Region × (MachineData → Prop) × (AS → Ctl → Prop) × UInt64) s c fs =>
    BoxPure (Ly) F0 n g.1 g.2.1 g.2.2.1 g.2.2.2 ∧ (At (Ly).exe (Ly).endPc g.1 g.2.1
      (bX ms0 (Ly).lab g.2.2.1 l b) s c ∧ TP g.2.2.2 s) ∧ QB l b l b c ∧ fs = []) fun g => ?_).mono_pre ?_
  · obtain ⟨R, F, J0, t⟩ := g
    by_cases hC : BoxPure (Ly) F0 n R F J0 t
    case neg => exact ⟨fun _ _ _ => False, fun _ _ _ h => hC h.1, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    have hp' := hP R F J0 t hC
    obtain ⟨⟨hR, -, hF, hlo, hhi⟩, -, -, ⟨⟨J, σC, rfl⟩, hdi, hst, hsp0⟩, ht, hn, -⟩ := hC
    have hfence : WcMidW (WB asm hp i E Dt Ctx ls0 l b n) (fun _ _ => False) (Ly).exe eR R F F
        (tpXa ms1 t) (WakeM.wJ0 (WakeM.wNC (Ly).lab J).J σC) (QB l b) :=
      WcMidW.mapWK (fun _ _ ⟨⟨hc, ha⟩, hw⟩ hk => ⟨⟨hw, WakeWc.pcOf_ne hc, WakeWc.pcOf_ne ha⟩, hk⟩)
        (WcMidW.and (WakeWc.wcMidW_offC hL) (wcMidW_w1 asm hp i E Dt Ctx ls0 l b n hp'.wcWf hp'.res hp'.tcb))
    have hseg := WakeWc.wake_wc_mid_hatW (p := X64WakeT1.wakeSrc)
      (lbl := Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b) (ms := ms1) (t := t) rfl (M := fun _ => True)
      (F₂ := F) hL rfl hF hR hlo hhi hF (fun _ h _ => h) (WakeWc.WcMidW.noSetFs hL rfl hfence)
      (by rintro l' A c ⟨rfl, -, ht, hh, ho, -⟩; exact ⟨ht, hh, _, ho⟩) (WakeOD.arW_pub hp i)
      hp'.resA hp'.hdrA hp'.tcbA hp'.tid (KStable.none F) (fun _ _ h => h.elim) hp'.ti
    have hseg := hseg.mono_K (K' := WakeH1Inv.K1W hp i E) fun s _ ⟨_, hc, ha⟩ s' =>
      ⟨fun h => (WakeWc.takeCKS_none (Cl := WakeOD.ClW hp i) (fun _ h => h.1)
        (fun e => ha (by rw [← haW]; unfold pcOf; rw [e])) hc s' h).elim, False.elim⟩
    refine SegWS.post_run (((SegWS.liftS [] hseg fun s c ⟨hw, hc, ha⟩ =>
      ⟨hw, WakeH1Inv.x1W_off hc (by rw [haW]; exact ha)⟩).mono_pre ?_).mono_post ?_)
    · rintro s c fs ⟨-, ⟨hA, htp⟩, hq, rfl⟩
      rw [hE] at hA
      exact ⟨⟨⟨l, b, at_bX_ms hokb ⟨hg.1.symm, hg.2.1.symm, hg.2.2.1.symm, hg.2.2.2.symm⟩ hA, hq⟩, htp⟩, rfl⟩
    · rintro s c fs ⟨⟨c0, ty, l', cA, m, fr, rfl, ⟨⟨rfl, hcA, -, -, ho, hme⟩, -, -, ho'⟩, hG, hGm, hA, hok, hat, hsp,
        htp⟩, rfl⟩
      have hty := congrArg Prod.fst (Option.some.inj (ho.symm.trans ho'))
      cases hty
      obtain ⟨c', hr, hsrc⟩ := pub_spawn (p := X64WakeT1.wakeSrc) (l := l') hme
      have hA' := at_wcNS_ctl (c' := c') hA
      have htb : t.toBitVec = (Ly).pinA + 0#64 + 8#64 := by
        apply BitVec.eq_of_toNat_eq
        have h1 := t.toBitVec.isLt; have h2 := (Ly).pinA.isLt; have ht' : t.toBitVec.toNat = _ := ht
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      obtain ⟨σe, ce, hJ, -, rfl⟩ := hGm
      have hm := hdi σe ce hJ
      have hσ := hsp0 σe ce hJ
      obtain ⟨rfl, -⟩ := hJ
      exact ⟨c', [], hr, rfl, hsrc, hn, (hp'.wcl s c' cA _ fr hA' hsrc).1, R, F, J, σC, cA, _, fr, t, hR, hlo, hhi,
        hst, hG, htb, htp, hA', hok, at_JS_ctl hat, hsp, hcA, hm, (hp'.wcl s c' cA _ fr hA' hsrc).2, hσ⟩
  · rintro s c fs ⟨⟨R, F, J0, t, h1, h2, h3, h4, ⟨hA, htp, ht⟩, hn, hsrc, -, h5⟩, rfl⟩
    exact ⟨(R, F, J0, t), ⟨h1, h2, h3, h4, ht, hn, h5⟩, ⟨hA, htp⟩, ⟨rfl, rfl, hsrc⟩, rfl⟩

end Inst

end Spike.Lib.X64.WakeHMid

/-- info: 'Spike.Lib.X64.WakeHMid.at_bX_ms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeHMid.at_bX_ms

/-- info: 'Spike.Lib.X64.WakeHMid.pub_spawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeHMid.pub_spawn

/-- info: 'Spike.Lib.X64.WakeHMid.at_wcNS_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeHMid.at_wcNS_ctl

/-- info: 'Spike.Lib.X64.WakeHMid.at_JS_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeHMid.at_JS_ctl

/-- info: 'Spike.Lib.X64.WakeHMid.hmid_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeHMid.hmid_box
