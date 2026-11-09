/-
**hello.w's spawned child's segment inside `ZR ∧ X`, landing in `X`** (x86-64; the twin of
`Spike/Lib/A64HelloWorkerSegRPX.lean`): the child's segment over `Spike/Lib/HelloSegTCSX.lean`'s `SegTCSX`,
composing the `X` links `Child.seg_childStubSX`, `Child.seg_thrWorkerSX` (`X64HelloThrTCSX`) and
`Wk.seg_wcWorkerSX` (`X64HelloWorkerTCSX`). The closed invariant of the result lies inside `X`
(`SegTCSX.closedX`), so `helloDR` reads `X`'s facts off every pair of it.

`X` at every landing pair: at the nodes from `ZObl` (`X64HelloWorkerSegRP`), and at the two landings off the
nodes from `ZXObl`: `print`'s return landing (`hXR`, the caller's return address with `print`'s control at
`[fr]`) and `wc_worker`'s return landing (`hXE`, the thread worker's `.x13` with `wc_worker`'s control at `[]`).

- `WcXObl`, `ZXObl`: `X` at the two landings off the nodes, per `wc_worker` region (`ZObl.hwc`'s data);
  `ZXObl.and`: at a conjunction.
- `seg_childRPXY`: from the stub's node at `[]` to `False`, inside `SH exe endPc (ZR exe kp ∧ Y ∧ X)`, landing in
  `X`, for a node-only fragment `Y` (`ZObl` only); `seg_childRPX`: at `Y := True` (`ZObl.triv`).
- `SegTCSX.toZHRPX`, `SegTCSX.toZHRPXY`: into `NNH ∧ ZHR exe kp ∧ X`, `NNH ∧ ZHR exe kp ∧ Y ∧ X`.
- `childPX cS`, `seg_childPPXc`: the stub node at some data whose premises hold, with word 3 the flag `cS`'s
  locative; its segment, the obligations asked under it; `seg_childPPXcY`: with `Y`.

## Differences from the AArch64 version

- `seg_childRPX` takes the premises as one `ChildPrem` (AArch64: unpacked); the thread worker runs in the
  re-based region `thrR R` from `sp0 - 8` (`Child.seg_childStubSX`), so the child's region is `R.lo ≤ -264`,
  `0 ≤ R.hi`, without alignment.
- `print`'s return landing (`hXR`) is in every `print` region with `R''.lo ≤ -72`, `16 ≤ R''.hi`, at
  `PrintF.cE … (-96) σC .ret`; the `wc_worker` regions (`hwcX`) are `R'.lo ≤ -176`, `8 ≤ R'.hi` at `.x13`, `wkJ`'s
  frame at `R'.addr 0`.
- `print`'s nodes at the call's `PrintF.cN` from `SegR.wcR_hZPc`.
- `seg_childPPX` is not twinned.
-/
import Spike.Lib.X64HelloWorkerSegRP
import Spike.Lib.X64HelloWorkerSegP
import Spike.Lib.X64HelloZSrc
import Spike.Lib.X64HelloSegTCSXC

namespace Spike.Lib.X64.Flow.Worker.Hello.SegRP

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.X64HelloSegTCSX
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloSplit (wcP wcR kid_splitH worker_find)
open Spike.Lib.X64HelloWorkerCallSrc (PrW KcW kcW_callI kcW_P0 kcW_done kcW_call)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words childN)
open Spike.Lib.X64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.X64.Flow.Worker.Hello.Z (ZR ZHR prW_notUnpk kcW_notPass wcP_notPass wcR_notPass c1_pass c2_pass)
open Spike.Lib.X64.Flow.Worker.Hello.SegR (kidH cS1 cS2 kidH_notPass ChildPrem ChildD wcR_hZPc)
open Spike.Lib.X64WakeMainR (XProW.and)
open Spike.Lib.X64.Flow.Worker.Wake.Child (thrR thrR_ok FStable.thrR)
open Scc.Cert.Rt.X64 (Lays endOf)
open SccCode (helloCells)

/-- **`X` at `wc_worker`'s two landings off its nodes** in a region `R'`, `F'` at a return `rbp`, `ra`
(`Wk.seg_wcWorkerSX`'s `hXR`, `hXE`): `print`'s return landing at `[fr]` in every `print` region whose frame
condition lands at the call node (`hXR`), and `wc_worker`'s return landing at `[]` (`hXE`). -/
structure WcXObl (X : FragS isa) (exe : _root_.Executable) (endPc : Int64) (R' : Region)
    (F' : MachineData → Prop) (rbp ra : BitVec 64) (w : Words) (tp : BitVec 64) (w0 w1 w2 w3 w4 : TermRun.Word)
    (n m : Nat) : Prop where
  hXR : ∀ fr (R'' : Region) (F'' : MachineData → Prop), R''.OK → R''.lo ≤ -72 → 16 ≤ R''.hi →
      FStable R'' F'' → (∀ m, F'' m → F' m) →
      PrintF.CallFC R' (Body.wCall (_root_.Executable.labels exe).label
        (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0)) (KcW w0 w1 w2 w3 w4 n m)) F'' → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0))
        (KcW w0 w1 w2 w3 w4 n m)).J σC c →
      CallToI helloSrc c cE fr →
      ∀ s c', At exe endPc R'' F'' (PrintF.cE (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m)
          (fun _ => PrW w0 w2 n m) (-96) σC .ret) s c' →
        X s c' [fr]
  hXE : ∀ s c, (∃ y, At exe endPc R' F' (HelloTail.E (cS2 w0 w1 w2 w3 w4) rbp ra tp y) s c) → X s c []

/-- **`X` at the landings off the nodes of the spawned child's run**: `WcXObl` in every `wc_worker` region
(`ZObl.hwc`'s data, at the return address `.x13`). -/
structure ZXObl (X : FragS isa) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (w : Words) (tp : BitVec 64) (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) :
    Prop where
  hwcX : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -176 → 8 ≤ R'.hi →
      FStable R' F' → (∀ m, F' m → F m) → ∀ rbp ra : BitVec 64,
      Int64.ofBitVec ra = (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x0" →
      WcXObl X exe endPc R' F' rbp ra w tp w0 w1 w2 w3 w4 n m

/-- **Two `ZXObl`s combine** (`X₁ ∧ X₂`). -/
theorem ZXObl.and {X₁ X₂ : FragS isa} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {w : Words} {tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (h₁ : ZXObl X₁ exe endPc R F w tp w0 w1 w2 w3 w4 n m) (h₂ : ZXObl X₂ exe endPc R F w tp w0 w1 w2 w3 w4 n m) :
    ZXObl (fun s c fs => X₁ s c fs ∧ X₂ s c fs) exe endPc R F w tp w0 w1 w2 w3 w4 n m where
  hwcX R' F' a b k d e rbp ra hra :=
    { hXR := fun fr R'' F'' a' b' c' d' e' hFC σC cc cE hJ hC s c'' hAt =>
        ⟨(h₁.hwcX R' F' a b k d e rbp ra hra).hXR fr R'' F'' a' b' c' d' e' hFC σC cc cE hJ hC s c'' hAt,
          (h₂.hwcX R' F' a b k d e rbp ra hra).hXR fr R'' F'' a' b' c' d' e' hFC σC cc cE hJ hC s c'' hAt⟩
      hXE := fun s c h => ⟨(h₁.hwcX R' F' a b k d e rbp ra hra).hXE s c h,
        (h₂.hwcX R' F' a b k d e rbp ra hra).hXE s c h⟩ }

/-- `ZXObl` is inhabited: at `X := True`. -/
example {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {w : Words}
    {tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat} :
    ZXObl (fun _ _ _ => True) exe endPc R F w tp w0 w1 w2 w3 w4 n m :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ => ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial, fun _ _ _ => trivial⟩⟩

/-- The abort's runs are all before the store. -/
theorem abortRuns_pre : abortRuns.all (fun q => (List.range q.2.2).all fun j =>
    !Spike.Lib.X64.PcRuns.inRuns helloCells Pass.helloPostRuns q.1 j) = true := by decide +kernel

section Seg

variable {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The spawned child's segment inside `SH exe endPc (ZR exe kp ∧ Y ∧ X)`, landing in `X`**: the child's
premises (`h`), a node-only fragment `Y` at every node (`ZObl`), `X` at every node (`ZObl`) and at the two landings
off the nodes (`ZXObl`). `Y` is asked at no landing: it is kept by the nodes only. -/
theorem seg_childRPXY {X Y : FragS isa} (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.X64.abi)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -264) (hhi : 0 ≤ R.hi)
    {w : Words} {tp sp0 : BitVec 64} {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (h : ChildPrem exe endPc kp lbl ms F w tp sp0 w0 w1 w2 w3 w4 n m)
    (hY : ZObl Y exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m)
    (hX₀ : ZObl X exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m)
    (hXX : ZXObl X exe endPc R F w tp w0 w1 w2 w3 w4 n m) :
    SegTCSX (SH exe endPc (fun s c fs => ZR exe kp s c fs ∧ Y s c fs ∧ X s c fs)) X helloSrc lbl ms
      ((At exe endPc R F (childN (_root_.Executable.labels exe).label (kidH T w0 w1 w2 w3 w4) w tp sp0)).at [])
      (fun _ _ _ => False) := by
  have hX := ZObl.and hY hX₀
  have hZX : ∀ s c fs, ZR exe kp s c fs ∧ Y s c fs ∧ X s c fs → X s c fs := fun _ _ _ h => h.2.2
  have hlo8 : R.lo ≤ -8 := by omega
  have hhi8 : -8 < R.hi := by omega
  have hRt := thrR_ok hR hlo8 hhi8
  have hFt := FStable.thrR hF hR hlo8 hhi8
  have hlot : (thrR R).lo ≤ -256 := show R.lo + 8 ≤ -256 by omega
  have hhit : 8 ≤ (thrR R).hi := show 8 ≤ R.hi + 8 by omega
  refine Child.seg_childStubSX (Z := fun s c fs => ZR exe kp s c fs ∧ Y s c fs ∧ X s c fs) hp hend hF hR (by omega)
    hhi hZX
    ?_ (fun i => NodeZA.and (Z.childR_hZc hp hend hR (by omega) hhi (kidH_notPass T w0 w1 w2 w3 w4) i) (hX.hZc i))
  refine Child.seg_thrWorkerSX (Z := fun s c fs => ZR exe kp s c fs ∧ Y s c fs ∧ X s c fs)
    (c1 := wcP w0 w1 w2 w3 w4) (c3 := cS2 w0 w1 w2 w3 w4) hp hend hFt hRt hlot hhit h.hlimT
    (kid_splitH worker_find w0 w1 w2 w3 w4).toLocalRun hZX ?_ (hK []) (ar := .unit) rfl h.hT h.hown h.hSx
    (XProW.and (Z.thrR_hz hp hend hRt (by omega) (by omega)
      fun _ _ hJ => by rw [hJ.1]; exact kidH_notPass T w0 w1 w2 w3 w4) hX.hzT)
    (NodeZA.and (Z.thrR_hZE hp hend hRt (by omega) hhit
      fun _ _ hJ => by rw [hJ.1]; exact kidH_notPass T w0 w1 w2 w3 w4) hX.hZEt)
    (fun i => NodeZA.and (Z.thrR_hZT hp hend hRt (by omega) hhit c2_pass i) (hX.hZT i))
  intro R' F' hR' hlo' hhi' hF' hFF rbp ra hra
  have hW := hX.hwc R' F' hR' hlo' hhi' hF' hFF rbp ra hra
  have hWX := hXX.hwcX R' F' hR' hlo' hhi' hF' hFF rbp ra hra
  exact Wk.seg_wcWorkerSX (Z := fun s c fs => ZR exe kp s c fs ∧ Y s c fs ∧ X s c fs)
    (cw := wcR w0 w1 w2 w3 w4) (c1 := cS1 w0 w1 w2 w3 w4) (c2 := cS2 w0 w1 w2 w3 w4)
    (X := fun σ => σ.regs.rsp.toBitVec = sp0 - 8#64 - 80#64)
    (Pr := fun _ => PrW w0 w2 n m) (Qa := fun _ => PrW w0 w2 n m) (Kc := KcW w0 w1 w2 w3 w4 n m)
    hp hend hF' hR' hlo' hhi'
    (fun σ c hJ hX' => (h.hlimW rbp ra σ c hJ hX').mono hFF)
    h.hm
    (fun σ fl hJ => kcW_call (g := fun σ => Body.wkC (_root_.Executable.labels exe).label σ fl) rfl
      (fun σ hJ => h.hx1 rbp ra _ σ fl hJ) σ hJ)
    (fun _ _ hk => kcW_callI hk) (fun _ _ _ _ hk hc => kcW_P0 h.hwm h.hm0 h.hwn hk hc)
    (fun _ _ _ _ _ _ _ hk hc hP => kcW_done hk hc hP) hK
    (fun fr R'' F'' hR'' hlo'' hhi'' hF'' hFF'' hFC σC c cE hJ hC =>
      h.hsvc rbp ra R' fr R'' F'' hR'' hlo'' hhi'' hF'' (fun m h => hFF m (hFF'' m h)) hFC σC c cE hJ hC
        (fun s c => Y s c [fr] ∧ X s c [fr])
        (NodeZA.toW (hW.hZP fr R'' F'' hR'' hlo'' hhi'' hF'' hFF'' hFC σC c cE hJ hC .sys)))
    (fun m hm => h.hdm m (hFF m hm))
    rfl rfl h.hv h.htag rfl (by simp [TermRun.cst, Promises.TVal.mk0, Scc.Sem.ValRep]) rfl
    (h.hS.mono hFF) h.htp4 rfl rfl rfl h.hvu rfl
    (XProW.and (Z.wcR_hz hp hend hR' (by omega) (by omega)
      fun _ _ hJ => by rw [hJ.1.1]; exact wcP_notPass w0 w1 w2 w3 w4) hW.hz)
    (by
      have hz := Z.wcR_hZE hp hend (F := F') (Pr := fun _ => PrW w0 w2 n m) hR' (by omega) hhi'
        (J := wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0))
        fun _ _ hJ => by rw [hJ.1]; exact wcP_notPass w0 w1 w2 w3 w4
      exact ⟨NodeZA.and hz.1 hW.hZE.1, NodeZA.and hz.2.1 hW.hZE.2.1, NodeZA.and hz.2.2 hW.hZE.2.2⟩)
    (NodeZA.and (Z.wcR_hZC hp hend hR' (by omega) hhi' fun _ _ hk => kcW_notPass hk) hW.hZC)
    (fun fr R'' F'' hR'' hlo'' hhi'' hF'' hFF'' hFC σC c cE hJ hC i =>
      NodeZA.and (wcR_hZPc hp hend hR'' (by omega) hhi'' (fun _ _ hq => prW_notUnpk hq)
        (fun _ _ hq => prW_notUnpk hq) i)
        (hW.hZP fr R'' F'' hR'' (by omega) hhi'' hF'' hFF'' hFC σC c cE hJ hC i))
    (fun fr RA FA hRA hloA hhiA hFA hFAF hFC σC c cE hJ hC k c' hQ =>
      (AbortObl.ofPc hp hend SccCode.hello_abort hFA hRA hloA hhiA fun _ he hpc _ hr =>
        Z.wcR_hZA hp hello_abortRunsOk abortRuns_pre (prW_notUnpk hQ) he hpc hr).and
        (hW.hZA fr RA FA hRA hloA hhiA hFA hFAF hFC σC c cE hJ hC k c' hQ))
    h.habt (fun fr s c hz => Z.wcR_hZu fr s c hz.1)
    (fun i => NodeZA.and (Z.wcR_hZW hp hend hR' (by omega) hhi'
      (wcR_notPass w0 w1 w2 w3 w4) c1_pass c2_pass i) (hW.hZW i))
    (fun R'' F'' hC rbp1 ra1 hra1 i =>
      NodeZA.and (Z.wcR_hZU hp hend hC.ok hC.lo hC.hi c1_pass c2_pass i) (hW.hZU R'' F'' hC rbp1 ra1 hra1 i))
    hZX hWX.hXR hWX.hXE

omit [Kraken.Executable.ValidLayout exe] in
/-- **`ZObl` at `True`.** -/
theorem ZObl.triv {w : Words} {tp sp0 : BitVec 64} {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat} :
    ZObl (fun _ _ _ => True) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m where
  hZc _ := BlkW.triv
  hzT := XProW.triv
  hZEt := BlkW.triv
  hZT _ := BlkW.triv
  hwc := by
    intros
    exact { hz := XProW.triv, hZE := ⟨BlkW.triv, BlkW.triv, BlkW.triv⟩, hZC := BlkW.triv
            hZP := by intros; exact BlkW.triv
            hZA := by intros; exact AbortObl.triv
            hZW := fun _ => BlkW.triv
            hZU := by intros; exact BlkW.triv }

/-- **The spawned child's segment inside `SH exe endPc (ZR exe kp ∧ X)`, landing in `X`**: the child's premises
(`h`), `X` at every node (`ZObl`) and at the two landings off the nodes (`ZXObl`); `seg_childRPXY` at
`Y := True`. -/
theorem seg_childRPX {X : FragS isa} (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.X64.abi)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -264) (hhi : 0 ≤ R.hi)
    {w : Words} {tp sp0 : BitVec 64} {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (h : ChildPrem exe endPc kp lbl ms F w tp sp0 w0 w1 w2 w3 w4 n m)
    (hX : ZObl X exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m)
    (hXX : ZXObl X exe endPc R F w tp w0 w1 w2 w3 w4 n m) :
    SegTCSX (SH exe endPc (fun s c fs => ZR exe kp s c fs ∧ X s c fs)) X helloSrc lbl ms
      ((At exe endPc R F (childN (_root_.Executable.labels exe).label (kidH T w0 w1 w2 w3 w4) w tp sp0)).at [])
      (fun _ _ _ => False) :=
  (seg_childRPXY hp hend hK hF hR hlo hhi h ZObl.triv hX hXX).mono_S
    fun _ _ _ h => ⟨h.1, ⟨h.2.1.1, h.2.1.2.2⟩, h.2.2⟩

end Seg

/-- **Into `helloDR`'s fragment** (`Z := ZHR ∧ X`): a segment inside `SH exe endPc (ZR exe kp ∧ X)` landing in
`X` is one inside `NNH ∧ ZHR exe kp ∧ X`. -/
theorem SegTCSX.toZHRPX {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isa} {exe : _root_.Executable} {endPc : Int64} {kp : Nat}
    {X P Q : FragS isa}
    (h : SegTCSX (SH exe endPc (fun s c fs => ZR exe kp s c fs ∧ X s c fs)) X p lbl ms P Q) :
    SegTCSX (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs ∧ X s c fs) X p lbl ms P Q :=
  h.mono_S fun _ _ _ h => ⟨h.1, h.2.1.1.toZHR h.2.2, h.2.1.2⟩

/-- **The child's entry with the packet's word 3 the flag `cS`**: at `[]`, the stub node at some data whose
premises hold and whose word 3 is `cS`'s locative (the clone's argument, bound by `spawn` to the flag's cell). -/
def childPX (exe : _root_.Executable) (endPc : Int64) (kp : Nat) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isa) (cS : WeakMem.Address) : FragS isa := fun s c fs =>
  fs = [] ∧ ∃ d : ChildD, d.ok ∧ ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m ∧
    d.w3.val = .loc cS 0 ∧
    At exe endPc d.R d.F (childN (_root_.Executable.labels exe).label (kidH d.T d.w0 d.w1 d.w2 d.w3 d.w4)
      d.w d.tp d.sp0) s c

/-- **The child's segment from `childPX cS`, landing in `X`**: never leaving, once `X` holds at every node
(`hX`) and at the landings off the nodes (`hXX`) at every datum whose word 3 is `cS`'s locative. -/
theorem seg_childPPXc {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat} {X : FragS isa}
    {cS : WeakMem.Address} (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.X64.abi)
    (hX : ∀ d : ChildD, d.ok →
      ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m → d.w3.val = .loc cS 0 →
      ZObl X exe endPc ms d.R d.F d.w d.tp d.sp0 d.T d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m)
    (hXX : ∀ d : ChildD, d.ok →
      ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m → d.w3.val = .loc cS 0 →
      ZXObl X exe endPc d.R d.F d.w d.tp d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m) :
    SegTCSX (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs ∧ X s c fs) X helloSrc lbl ms
      (childPX exe endPc kp lbl ms cS) (fun _ _ _ => False) := by
  refine SegTCSX.toZHRPX ((SegTCSX.exists_pre fun d : ChildD => SegTCSX.of_imp
    (A := d.ok ∧ ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m ∧
      d.w3.val = .loc cS 0)
    (P := (At exe endPc d.R d.F (childN (_root_.Executable.labels exe).label
      (kidH d.T d.w0 d.w1 d.w2 d.w3 d.w4) d.w d.tp d.sp0)).at []) fun ⟨hok, h, hcS⟩ =>
      have ⟨hF, hR, hlo, hhi⟩ := hok
      seg_childRPX hp hend hK hF hR hlo hhi h (hX d hok h hcS) (hXX d hok h hcS)).mono_pre ?_)
  rintro s c fs ⟨rfl, d, hok, hpr, hcS, hA⟩
  exact ⟨d, ⟨hok, hpr, hcS⟩, hA, rfl⟩

/-- **Into `helloDR`'s fragment with a node-only `Y`** (`Z := ZHR ∧ Y ∧ X`; `SegTCSX.toZHRPX` with `Y`). -/
theorem SegTCSX.toZHRPXY {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isa} {exe : _root_.Executable} {endPc : Int64} {kp : Nat}
    {X Y P Q : FragS isa}
    (h : SegTCSX (SH exe endPc (fun s c fs => ZR exe kp s c fs ∧ Y s c fs ∧ X s c fs)) X p lbl ms P Q) :
    SegTCSX (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs ∧ Y s c fs ∧ X s c fs) X p lbl ms P Q :=
  h.mono_S fun _ _ _ h => ⟨h.1, h.2.1.1.toZHR h.2.2, h.2.1.2⟩

/-- **The child's segment from `childPX cS` with a node-only `Y`, landing in `X`** (`seg_childPPXc` with `Y`
at every node, `hY`, at every datum whose word 3 is `cS`'s locative). -/
theorem seg_childPPXcY {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat} {X Y : FragS isa}
    {cS : WeakMem.Address} (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.X64.abi)
    (hY : ∀ d : ChildD, d.ok →
      ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m → d.w3.val = .loc cS 0 →
      ZObl Y exe endPc ms d.R d.F d.w d.tp d.sp0 d.T d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m)
    (hX : ∀ d : ChildD, d.ok →
      ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m → d.w3.val = .loc cS 0 →
      ZObl X exe endPc ms d.R d.F d.w d.tp d.sp0 d.T d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m)
    (hXX : ∀ d : ChildD, d.ok →
      ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m → d.w3.val = .loc cS 0 →
      ZXObl X exe endPc d.R d.F d.w d.tp d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m) :
    SegTCSX (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs ∧ Y s c fs ∧ X s c fs) X helloSrc lbl ms
      (childPX exe endPc kp lbl ms cS) (fun _ _ _ => False) := by
  refine SegTCSX.toZHRPXY ((SegTCSX.exists_pre fun d : ChildD => SegTCSX.of_imp
    (A := d.ok ∧ ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m ∧
      d.w3.val = .loc cS 0)
    (P := (At exe endPc d.R d.F (childN (_root_.Executable.labels exe).label
      (kidH d.T d.w0 d.w1 d.w2 d.w3 d.w4) d.w d.tp d.sp0)).at []) fun ⟨hok, h, hcS⟩ =>
      have ⟨hF, hR, hlo, hhi⟩ := hok
      seg_childRPXY hp hend hK hF hR hlo hhi h (hY d hok h hcS) (hX d hok h hcS) (hXX d hok h hcS)).mono_pre ?_)
  rintro s c fs ⟨rfl, d, hok, hpr, hcS, hA⟩
  exact ⟨d, ⟨hok, hpr, hcS⟩, hA, rfl⟩

end Spike.Lib.X64.Flow.Worker.Hello.SegRP

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SegRP.seg_childRPX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SegRP.seg_childRPX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SegRP.seg_childPPXc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SegRP.seg_childPPXc

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SegRP.seg_childRPXY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SegRP.seg_childRPXY

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SegRP.seg_childPPXcY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SegRP.seg_childPPXcY
