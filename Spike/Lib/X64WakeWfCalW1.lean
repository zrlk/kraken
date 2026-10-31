/-
**wake.w's `wc_main` callees inside `h1`'s level `W1W`** (x86-64): the
`hres`/`htcb` premises of `WakeWc.wcMidW_w1`, from `X64WakeWfCal`'s
`reserveW_wfG`/`tcbWG_wfG` at `Ly := RuntimeLayout.ofPlaceWX hpw i`, the
canonical target's marks rewritten to `PhRec.μ Ly` (`AbOffW.marks_target`).

- `blkW_noK`, `nodeW_noK`, `reserveW_noK`, `tcbWG_noK`: a node family inside
  `W` at any move inside a weaker `W'` at no move.
- `reserveW_vac`: every `ReserveW` node holds at a frame condition that holds
  for no memory.
- `reserveW_wf`: `hres`. The nodes' `SFactsSt2` (`hst`, at any move) and
  placement (`hpl`) given; the reserve's control from the source's
  (`hSctl`, via `ResCtx`).
- `tcbWG_wf_pt`, `tcbWG_wf`: `htcb`. The nodes' `SFactsSt2` (`hst`, e.g.
  `OwnTcb2.tcb2W_ownGX`) and placement (`hpl`) given; the callee's control
  from the source's (`hSctl`, via `MidG`).

Where x86-64 differs from AArch64: the layout is `RuntimeLayout.ofPlaceWX`
at `PlaceWX`, the level `W1W` takes the assembly `asm` (`hpa : cellsOf asm =
some o.prog`; A64's `textProgram … = .ok o.prog`) and owns `ownGXW`
(`ownG` with the TCB self words; A64's `ownG`); no `hal`. The reserve's
region is `rAR R = R.callee (-72) (-40) 8` (`hRlo : R.lo ≤ -112`, `hhi :
-64 ≤ R.hi`; A64's `R.callee (-80) (-48) 0`, `-128`, `0`) and its
frame condition carries `CallerCells R (-72) (-40) 8` and `ResCtx` at
x86-64's `rN … R …`; the reserve's source is `Q` (A64's `S`). The callee of
the second TCB is in `R.callee (-72) (-184) 8` (`hRlo : R.lo ≤ -256`,
`hhi : -64 ≤ R.hi`; A64's `R.callee (-80) (-192) 0`, `-272`, `0`) at
`wcMidW_w1`'s shape: every `c0 cA m fr` with `MidG`/`FrG`/`FrMG`, the frame
condition with `TcbCtx` (A64: every `c0` of `S`). `reserveW_wf` takes the
nodes' `SFactsSt2` at `ownGXW` as a premise `hst` (A64 builds them at
`ownG` from `WcW.reserveW_wcG`, with its `hsep`, `hmN`), as `tcbWG_wf` does.
`tcbWG_wf_pt` is stated at the callee's region and frame condition and the
control's facts (A64: at `wc_main`'s region and a control of `S`), since
x86-64's frame condition depends on the frame ghosts `cA m fr`.
-/
import Spike.Lib.X64WakeWfCal
import Spike.Lib.X64WakeWcW1
import Spike.Lib.X64WakeAbOffW
import Spike.Lib.X64SiteOfPlaceW

namespace Spike.Lib.X64.WakePh.CalWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout TcbWG)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.Rt.Reserve (ReserveW ntA)
open Spike.Lib.X64.Flow.WakeWc (rN rAR ResCtx MidG FrG FrMG TcbCtx wcNCR)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64WakeT1 (wakeSrc)
open Spike.Lib (Region FragS PlaceWX)

section NoK

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W W' : Frag isa} {K : State → State → Prop}

/-- A block inside `W` at `K` is inside a weaker `W'` at no move. -/
theorem blkW_noK {n : ND} {blk : List (Directive × Nat)} (h : BlkW W K exe endPc R F n blk)
    (hw : ∀ s c, W s c → W' s c) :
    BlkW W' (fun _ _ => False) exe endPc R F n blk := fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
  ⟨hw _ _ (h s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9).1, fun _ h => h⟩

/-- A node inside `W` at `K` is inside a weaker `W'` at no move. -/
theorem nodeW_noK {n : ND} (h : NodeW W K exe endPc R F n) (hw : ∀ s c, W s c → W' s c) :
    NodeW W' (fun _ _ => False) exe endPc R F n := fun s c hA => ⟨hw _ _ (h s c hA).1, fun _ h => h⟩

/-- `ReserveW` inside `W` at `K` is inside a weaker `W'` at no move. -/
theorem reserveW_noK {q : Spike.Lib.X64.Rt.Reserve.ResG} (h : ∀ i, ReserveW W K exe endPc R F q i)
    (hw : ∀ s c, W s c → W' s c) : ∀ i, ReserveW W' (fun _ _ => False) exe endPc R F q i := by
  intro i; have h := h i
  cases i <;> dsimp only [ReserveW] at h ⊢ <;> first | exact blkW_noK h hw | exact nodeW_noK h hw

/-- `TcbWG` inside `W` at `K` is inside a weaker `W'` at no move. -/
theorem tcbWG_noK {q : Spike.Lib.X64.Rt.TcbGG} (h : ∀ i, TcbWG W K exe endPc R F q i)
    (hw : ∀ s c, W s c → W' s c) : ∀ i, TcbWG W' (fun _ _ => False) exe endPc R F q i := by
  intro i; have h := h i
  cases i <;> dsimp only [TcbWG] at h ⊢ <;> first | exact blkW_noK h hw | exact nodeW_noK h hw

/-- **`ReserveW` at a frame condition holding for no memory.** -/
theorem reserveW_vac {q : Spike.Lib.X64.Rt.Reserve.ResG} (hF : ∀ m, ¬ F m) :
    ∀ i, ReserveW W K exe endPc R F q i := by
  intro i
  cases i <;> dsimp only [ReserveW] <;>
    first
    | exact fun _ _ _ _ _ _ _ _ hF' => (hF _ hF').elim
    | exact fun _ _ ⟨_, _, _, _, _, _, hF', _⟩ => (hF _ hF').elim

end NoK

section W1

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option maxHeartbeats 1600000 in
/-- **`wcMidW_w1`'s `hres`**: the reserve's nodes inside `W1W asm … l b n`
at no frames, for every frame ghost and control returning to `.x19`, in
the reserve's region `rAR R`. The source's controls are not `main`'s `ret`
and their runs are well formed (`hSctl`); the counter `scc_rt_nthreads` is
unmapped under `F` (`hunN`), off wake's arena and not its counter word
(`hoffN`); the nodes' `SFactsSt2` (`hst`, at any move) and frames' placement
(`hpl`) are given. -/
theorem reserveW_wf (asm : Scc.Sem.X64.Asm) (E : Scc.Sem.Entry)
    (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Spike.Lib.X64Consumer.Lsize) (l : WeakMem.AllocLabel)
    (b n : Nat) (hpg : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = lo)
    (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {J0 : Spike.Lib.X64.AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} {K' : State → State → Prop}
    (hR : R.OK) (hRlo : R.lo ≤ -112) (hhi : -64 ≤ R.hi)
    (hSctl : ∀ l A c, Q l A c → (∀ a, c.term ≠ .ret a) ∧ RunWf wakeSrc c [])
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none)
    (hoffN : ¬ ((WakeOD.arW hpw i).heap ≤ (ntA (Ly).lab).toNat ∧
        (ntA (Ly).lab).toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨ntA (Ly).lab, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc)
    (hst : ∀ g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G × Ctl, g.1.ra = ((Ly).lab ".Lwc_main.x19").toBitVec →
      ∀ nd, ReserveW (fun s _ => SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (ownGXW (Ly) (ntA (Ly).lab)) s) K'
        (Ly).exe (Ly).endPc (rAR R)
        (fun m => F m ∧ CallerCells R (-72) (-40) 8 m ∧ ResCtx (Ly).lab R (rN ms (Ly).lab R J0 Q .call).J g m)
        ⟨g.1, 0#64, g.2⟩ nd)
    (hpl : ∀ g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G × Ctl, g.1.ra = ((Ly).lab ".Lwc_main.x19").toBitVec →
      ∀ nd, ReserveW (fun s c => PlacedSE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b)
          s c []) (fun _ _ => False) (Ly).exe (Ly).endPc (rAR R)
        (fun m => F m ∧ CallerCells R (-72) (-40) 8 m ∧ ResCtx (Ly).lab R (rN ms (Ly).lab R J0 Q .call).J g m)
        ⟨g.1, 0#64, g.2⟩ nd) :
    ∀ g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G × Ctl, g.1.ra = ((Ly).lab ".Lwc_main.x19").toBitVec →
      ∀ nd, ReserveW (fun s c => WakeOPremW.W1W asm hpw i E Dt Ctx ls0 l b n s c []) (fun _ _ => False)
        (Ly).exe (Ly).endPc (rAR R)
        (fun m => F m ∧ CallerCells R (-72) (-40) 8 m ∧ ResCtx (Ly).lab R (rN ms (Ly).lab R J0 Q .call).J g m)
        ⟨g.1, 0#64, g.2⟩ nd := by
  intro g hra
  have hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => PlaceWX.hlab_ofPlaceWX hpw i l x (by rw [hlo, hpg]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName := PlaceWX.abortLbl_of_placeWX (PlaceWX.link i hpw)
  have hsite := PlaceWX.site_ofPlaceWX hpw i
  have hpL : (Ly).prog = wakeCells := hpg
  by_cases hS : ∃ l' A', Q l' A' g.2
  · obtain ⟨l', A', hs⟩ := hS
    have hc := hSctl _ _ _ hs
    have hR' : (rAR R).OK := Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
    have hW := reserveW_wfG (Dt := Dt) (ar := WakeOD.arW hpw i) (p := wakeSrc) (Cl := WakeOD.ClW hpw i)
      (Ctx := fun _ _ _ => False) (lsize := Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n)
      (fs := []) hpL hlo hΛ hlab hsite (fun _ h => h.2) hR' (by simp [Region.callee])
      (by simp [Region.callee]) ⟨g.1, 0#64, g.2⟩ hra ⟨fun _ => hc.1, hc.2⟩ (fun m hm => hunN m hm.1)
      hoffN (hst g hra) (hpl g hra)
    intro nd
    unfold WakeOPremW.W1W Spike.Lib.X64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
    rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
    exact reserveW_noK hW (fun _ _ h => h) nd
  · refine reserveW_vac fun m hm => hS ?_
    obtain ⟨_, _, c, _, ⟨⟨l', A', _, hs⟩, _⟩, ⟨hc, _⟩, _⟩ := hm.2.2
    exact ⟨l', A', by rw [← show c = g.2 from hc]; exact hs⟩

set_option maxHeartbeats 1600000 in
/-- **`tcbWG_wf` at one source control `c0` and ghost `g`**, `hst`/`hpl` at
those, in the callee's region `Rc` and frame condition `Fc`. -/
theorem tcbWG_wf_pt (asm : Scc.Sem.X64.Asm) (E : Scc.Sem.Entry)
    (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Spike.Lib.X64Consumer.Lsize) (l : WeakMem.AllocLabel)
    (b n : Nat) (hpg : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = lo)
    (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    {Rc : Region} {Fc : MachineData → Prop} {K' : State → State → Prop}
    (hR : Rc.OK) (hRlo : Rc.lo ≤ -184) (hhi : 8 ≤ Rc.hi)
    (hunP : ∀ m, Fc m → Mem.loadInt m.dmem (Ly).pnA 8 = none)
    (hoffP : ¬ ((WakeOD.arW hpw i).heap ≤ (Ly).pnA.toNat ∧
        (Ly).pnA.toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨(Ly).pnA, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc)
    (hunH : ∀ m, Fc m → Mem.loadInt m.dmem ((Ly).pinA + 96#64) 8 = none)
    (hoffH : ¬ ((WakeOD.arW hpw i).heap ≤ ((Ly).pinA + 96#64).toNat ∧
        ((Ly).pinA + 96#64).toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨(Ly).pinA + 96#64, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc)
    (c0 : Ctl) (hc : (∀ a, c0.term ≠ .ret a) ∧ RunWf wakeSrc c0 []) (g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G)
    (hra : g.ra = ((Ly).lab ".Lwc_main.x20").toBitVec)
    (hst : ∀ nd, TcbWG (fun s _ => SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (ownGXW (Ly) (ntA (Ly).lab)) s) K'
        (Ly).exe (Ly).endPc Rc Fc (Tcb2Call.tcb2Q g c0) nd)
    (hpl : ∀ nd, TcbWG (fun s c => PlacedSE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b)
        s c []) (fun _ _ => False) (Ly).exe (Ly).endPc Rc Fc (Tcb2Call.tcb2Q g c0) nd) :
    ∀ nd, TcbWG (fun s c => WakeOPremW.W1W asm hpw i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe
      (Ly).endPc Rc Fc (Tcb2Call.tcb2Q g c0) nd := by
  have hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => PlaceWX.hlab_ofPlaceWX hpw i l x (by rw [hlo, hpg]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName := PlaceWX.abortLbl_of_placeWX (PlaceWX.link i hpw)
  have hsite := PlaceWX.site_ofPlaceWX hpw i
  have hpL : (Ly).prog = wakeCells := hpg
  have hW := tcbWG_wfG (Dt := Dt) (ar := WakeOD.arW hpw i) (p := wakeSrc) (Cl := WakeOD.ClW hpw i)
    (Ctx := fun _ _ _ => False) (lsize := Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n)
    (fs := []) hpL hlo hΛ hlab hsite (fun _ h => h.2) hR hRlo hhi g c0 hra ⟨fun _ => hc.1, hc.2⟩
    hunP hoffP hunH hoffH hst hpl
  intro nd
  unfold WakeOPremW.W1W Spike.Lib.X64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
  rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
  exact tcbWG_noK hW (fun _ _ h => h) nd

/-- **`wcMidW_w1`'s `htcb`**: the second TCB's `scc_rt_alloc_tcb` nodes
inside `W1W asm … l b n` at no frames, at every control of the source with
its frame ghosts (`MidG`, `FrG`, `FrMG`) and ghost returning to `.x20`, in
the callee's region `R.callee (-72) (-184) 8` of `wc_main`'s `R`. The
source's controls are not `main`'s `ret` and their runs are well formed
(`hSctl`); the nodes' `SFactsSt2` (`hst`, at any move) and placement
(`hpl`) are given; the counter `scc_rt_pinned_next` and the header word
`scc_rt_pinned + 96` are unmapped under `F` (`hunP`, `hunH`), off wake's
arena and not its counter word (`hoffP`, `hoffH`). -/
theorem tcbWG_wf (asm : Scc.Sem.X64.Asm) (E : Scc.Sem.Entry)
    (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Spike.Lib.X64Consumer.Lsize) (l : WeakMem.AllocLabel)
    (b n : Nat) (hpg : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = lo)
    (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    {R : Region} {F : MachineData → Prop} {J0 : Spike.Lib.X64.AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} {K' : State → State → Prop}
    (hR : R.OK) (hRlo : R.lo ≤ -256) (hhi : -64 ≤ R.hi)
    (hSctl : ∀ l A c, Q l A c → (∀ a, c.term ≠ .ret a) ∧ RunWf wakeSrc c [])
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none)
    (hoffP : ¬ ((WakeOD.arW hpw i).heap ≤ (Ly).pnA.toNat ∧
        (Ly).pnA.toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨(Ly).pnA, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 96#64) 8 = none)
    (hoffH : ¬ ((WakeOD.arW hpw i).heap ≤ ((Ly).pinA + 96#64).toNat ∧
        ((Ly).pinA + 96#64).toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨(Ly).pinA + 96#64, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc)
    (hst : ∀ c0 cA m fr, MidG Q c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
      ∀ g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G, g.ra = ((Ly).lab ".Lwc_main.x20").toBitVec →
      ∀ nd, TcbWG (fun s _ => SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (ownGXW (Ly) (ntA (Ly).lab)) s) K'
        (Ly).exe (Ly).endPc (R.callee (-72) (-184) 8) (fun mm => F mm ∧ CallerCells R (-72) (-184) 8 mm ∧
          TcbCtx (Ly).lab R (wcNCR (Ly).lab c0 cA m fr).J c0 g mm) (Tcb2Call.tcb2Q g c0) nd)
    (hpl : ∀ c0 cA m fr, MidG Q c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
      ∀ g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G, g.ra = ((Ly).lab ".Lwc_main.x20").toBitVec →
      ∀ nd, TcbWG (fun s c => PlacedSE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b)
          s c []) (fun _ _ => False) (Ly).exe (Ly).endPc (R.callee (-72) (-184) 8)
        (fun mm => F mm ∧ CallerCells R (-72) (-184) 8 mm ∧ TcbCtx (Ly).lab R (wcNCR (Ly).lab c0 cA m fr).J c0 g mm)
        (Tcb2Call.tcb2Q g c0) nd) :
    ∀ c0 cA m fr, MidG Q c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
      ∀ g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G, g.ra = ((Ly).lab ".Lwc_main.x20").toBitVec →
      ∀ nd, TcbWG (fun s c => WakeOPremW.W1W asm hpw i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe
        (Ly).endPc (R.callee (-72) (-184) 8)
        (fun mm => F mm ∧ CallerCells R (-72) (-184) 8 mm ∧ TcbCtx (Ly).lab R (wcNCR (Ly).lab c0 cA m fr).J c0 g mm)
        (Tcb2Call.tcb2Q g c0) nd := by
  intro c0 cA m fr hG g hra
  obtain ⟨l', A', hs, -⟩ := hG.1
  have hR' : (R.callee (-72) (-184) 8).OK := Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  exact tcbWG_wf_pt hpw i asm E Dt Ctx ls0 l b n hpg hlo hpa hR' (by simp [Region.callee])
    (by simp [Region.callee]) (fun mm hm => hunP mm hm.1) hoffP (fun mm hm => hunH mm hm.1) hoffH c0
    (hSctl _ _ _ hs) g hra (hst c0 cA m fr hG g hra) (hpl c0 cA m fr hG g hra)

end W1

end Spike.Lib.X64.WakePh.CalWf

/-- info: 'Spike.Lib.X64.WakePh.CalWf.reserveW_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.CalWf.reserveW_wf

/-- info: 'Spike.Lib.X64.WakePh.CalWf.tcbWG_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.CalWf.tcbWG_wf

/-- info: 'Spike.Lib.X64.WakePh.CalWf.tcbWG_wf_pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.CalWf.tcbWG_wf_pt
