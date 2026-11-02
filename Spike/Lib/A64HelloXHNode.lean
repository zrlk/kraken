/-
**`XH` at every node of the spawned child's run** (AArch64; rows 5j-wit-W, 5j-wit-E-call): `SegRP.ZObl (XH Λ lbl)`,
the `hX` input of `XH.zObl_XHF`, from `ZObl` at `PlacedSE` and the layout's lack of
immediates at the child's and the call's terms.

`XH`'s second conjunct is `PlacedSE`'s consequence at the node's pinned control: at `kidH` (the stub, the thread
worker's prologue and head) by `XH.xh3_kid`; at `wcP` (`wc_worker`'s prologue, head and call) by `XH.xh3_wcP`;
at `wcRE`, `cS1`, `cS2` (the tail, `scc_rt_unpark`, the thread worker's tail) vacuously, as no local run from
them reaches the call (`wcRE`'s store takes no local step given the flag word `hcS`, `cS1`'s extern none,
`cS2`'s `ret` none). On `print`'s nodes and its abort path the stack is `[fr]`, so only `PlacedSE` is left.

- `NodeZA.monoJ`, `NodeW.monoJ`, `ProW.monoJ`: a node obligation weakened at the node's controls.
- `H3`: `XH`'s second conjunct; `xh_of`: `XH` on no frame from `PlacedSE` and `H3`; `xh_fr`: `XH` on a frame.
- `h3_kidH`, `h3_wcP`, `h3_wcRE`, `h3_cS1`, `h3_cS2`: `H3` at the pinned controls.
- `wcObl_XH`, `zObl_XH`: `WcObl` and `ZObl` at `XH`.
- `iH_wcall`: the root's table has no immediate at `print`'s call (with `XH.iH_kid`, `zObl_XH`'s layout premises).
-/
import Spike.Lib.A64HelloXHF
import Spike.Lib.A64HelloFlagObl

namespace Spike.Lib.A64.HelloPh.XHNode

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (wcP workerCallH workerRestH)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (kidH cS1 cS2)
open Spike.Lib.A64.Flow.Worker.Hello.SegRP (WcObl ZObl)
open Spike.Lib.A64.Flow.Worker.Hello.FlagSrc (wcRE wcRE_noStep)
open Spike.Lib.A64.HelloPh.XH (XH kidC xh3_kid xh3_wcP)

/-! ## Node obligations weakened at the node's controls -/

section Gen

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {Z Z' : Frag isaLSE2}

/-- **A block node's fact weakened at the node's controls.** -/
theorem NodeZA.monoJ {n : ND} {blk : List Directive} (h : NodeZA Z exe endPc R F n blk)
    (hZ : ∀ σ c, n.J σ c → ∀ s, Z s c → Z' s c) : NodeZA Z' exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hD hJ k hk m hA' hD' =>
    ⟨hZ σ c hJ _ (h s σ c he hn hd hpc hA hD hJ k hk m hA' hD').1, fun _ h => h⟩

/-- **A node's obligation weakened at the node's controls.** -/
theorem NodeW.monoJ {n : ND} (h : NodeW Z (fun _ _ => False) exe endPc R F n)
    (hZ : ∀ σ c, n.J σ c → ∀ s, Z s c → Z' s c) : NodeW Z' (fun _ _ => False) exe endPc R F n :=
  fun s c hs => ⟨by
    have h1 := (h s c hs).1
    obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := hs
    exact hZ σ c hJ s h1, fun _ h => h⟩

/-- **A prologue's obligation weakened at its entry's controls.** -/
theorem ProW.monoJ {ms : MemSide isaLSE2} {pc0 Zr lim : Int64} {L : Label} {ps : List (XReg × Int64)}
    {J : Spike.Lib.A64.Flow.AS → Ctl → Prop} (h : ProW Z (fun _ _ => False) exe endPc R F ms pc0 Zr lim L ps J)
    (hZ : ∀ σ c, J σ c → ∀ s, Z s c → Z' s c) : ProW Z' (fun _ _ => False) exe endPc R F ms pc0 Zr lim L ps J :=
  ⟨NodeZA.monoJ h.w0 hZ, NodeW.monoJ h.w1 fun _ c ⟨σ0, hJ, _⟩ => hZ σ0 c hJ,
    NodeZA.monoJ h.w2 fun _ c ⟨σ0, _, hJ, _⟩ => hZ σ0 c hJ, NodeZA.monoJ h.w3 fun _ c ⟨σ0, _, hJ, _⟩ => hZ σ0 c hJ⟩

end Gen

/-! ## `XH`'s second conjunct at the pinned controls -/

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {w0 w1 w2 w3 w4 : TermRun.Word}

/-- **`XH`'s second conjunct**: the caller frame of a call of `print` the control runs to placed. -/
def H3 (Λ : Scc.Sem.Layout) (lbl : Lbl) (s : State) (c : Ctl) : Prop :=
  ∀ c', LocalRunS helloSrc c c' → c'.term = workerCallH → FramesPlaced Λ lbl s [⟨"u", workerRestH, c'.env, [], .unit⟩]

/-- `XH` on no frame from `PlacedSE` and `H3`. -/
theorem xh_of {s : State} {c : Ctl} (hp : PlacedSE Λ lbl s c []) (h3 : H3 Λ lbl s c) : XH Λ lbl s c [] :=
  ⟨hp, fun _ => h3⟩

/-- `XH` on a frame is `PlacedSE`. -/
theorem xh_fr {fr : TermRun.Frame} {s : State} {c : Ctl} (hp : PlacedSE Λ lbl s c [fr]) : XH Λ lbl s c [fr] :=
  ⟨hp, fun h => absurd h (List.cons_ne_nil _ _)⟩

/-- **`H3` at the child's control** from its `PlacedSE`. -/
theorem h3_kidH {T : Ty} (hik : ∀ y k, Λ.imms (kidC T w0 w1 w2 w3 w4).term y k = none) {s : State} {c : Ctl}
    (e : c = kidH T w0 w1 w2 w3 w4) (hp : PlacedSE Λ lbl s c []) : H3 Λ lbl s c := by
  subst e; exact xh3_kid hp hik

/-- **`H3` at `print`'s call** from its `PlacedSE`. -/
theorem h3_wcP (hiw : ∀ y k, Λ.imms workerCallH y k = none) {s : State} {c : Ctl} (e : c = wcP w0 w1 w2 w3 w4)
    (hp : PlacedSE Λ lbl s c []) : H3 Λ lbl s c := by
  subst e; exact xh3_wcP hp hiw

/-- **`H3` at the store after `print`'s return**: it takes no local step. -/
theorem h3_wcRE {cS : WeakMem.Address} (hcS : w3.val = .loc cS 0) {ws : List TermRun.Word} {s : State} {c : Ctl}
    (e : c = wcRE w0 w1 w2 w3 w4 ws) : H3 Λ lbl s c := by
  subst e
  intro c' hr ht
  cases hr with
  | refl => simp [wcRE, workerRestH, workerCallH] at ht
  | step hs _ => exact (wcRE_noStep hcS hs).elim

/-- **`H3` at the `unpark`**: the extern takes no local step. -/
theorem h3_cS1 {s : State} {c : Ctl} (e : c = cS1 w0 w1 w2 w3 w4) : H3 Λ lbl s c := by
  subst e
  intro c' hr ht
  cases hr with
  | refl => simp [cS1, workerCallH] at ht
  | step hs _ => exact (PrintSvc.LocalStepS.not_ext hs rfl).elim

/-- **`H3` at the return**: a `ret` takes no local step. -/
theorem h3_cS2 {s : State} {c : Ctl} (e : c = cS2 w0 w1 w2 w3 w4) : H3 Λ lbl s c := by
  subst e
  intro c' hr ht
  cases hr with
  | refl => simp [cS2, workerCallH] at ht
  | step hs _ => exact (hs.not_ret _ rfl).elim

/-! ## `ZObl` at `XH` -/

variable {exe : _root_.Executable} {endPc : Int64} {ms : List TermRun.Frame → MemSide isaLSE2}
  {w : Hello.Child.Words} {tp sp0 : BitVec 64} {n m : Nat} {cS : WeakMem.Address}

/-- **`WcObl` at `XH`** from `WcObl` at `PlacedSE`: `wc_worker`'s prologue, head and call at `wcP`, the tail
and `scc_rt_unpark` at `wcRE`, `cS1`, `cS2`, `print`'s nodes and abort path on a frame. -/
theorem wcObl_XH (hcS : w3.val = .loc cS 0) (hiw : ∀ y k, Λ.imms workerCallH y k = none)
    {R' : Region} {F' : MachineData → Prop} {x29 ra : BitVec 64}
    (hP : WcObl (fun s c fs => PlacedSE Λ lbl s c fs) exe endPc ms R' F' x29 ra w tp sp0 w0 w1 w2 w3 w4 n m) :
    WcObl (XH Λ lbl) exe endPc ms R' F' x29 ra w tp sp0 w0 w1 w2 w3 w4 n m where
  hz := ProW.monoJ hP.hz fun _ _ hJ _ hp => xh_of hp (h3_wcP hiw hJ.1.1 hp)
  hZE := NodeZA.monoJ hP.hZE fun _ _ hJ _ hp => xh_of hp (h3_wcP hiw hJ.1 hp)
  hZC := NodeW.monoJ hP.hZC fun _ _ hJ _ hp => xh_of hp (h3_wcP hiw hJ.2.1 hp)
  hZP fr R'' F'' a b c d e f g σC cc cE hJ hC i :=
    NodeZA.mono (hP.hZP fr R'' F'' a b c d e f g σC cc cE hJ hC i) fun _ _ hp => xh_fr hp
  hZA fr RA FA a b c d e f g σC cc cE hJ hC k c' hQ :=
    (hP.hZA fr RA FA a b c d e f g σC cc cE hJ hC k c' hQ).mono fun _ _ hp => xh_fr hp
  hZW i := NodeZA.monoJ (hP.hZW i) fun _ _ hJ _ hp => by
    cases i
    case sp4 => exact xh_of hp (h3_wcRE hcS hJ.1)
    case st => exact xh_of hp (h3_wcRE hcS hJ.1.1)
    case n3 => exact xh_of hp (h3_cS1 hJ.1)
    case bl | unpk => exact xh_of hp (h3_cS1 hJ.1.1)
    case sp6 => exact xh_of hp (h3_cS2 hJ.1)
  hZU R'' F'' a b c d e f x29' ra' g i := NodeZA.monoJ (hP.hZU R'' F'' a b c d e f x29' ra' g i) fun _ _ hJ _ hp => by
    cases i
    case e | n1 => exact xh_of hp (h3_cS1 hJ.1)
    case swp => exact xh_of hp (h3_cS1 hJ.1.1)
    case svc => exact xh_of hp (h3_cS2 hJ.1.1)
    all_goals exact xh_of hp (h3_cS2 hJ.1)

/-- **`ZObl` at `XH`** from `ZObl` at `PlacedSE`: the stub and the thread worker's
prologue and head at `kidH`, its tail at `cS2`, `wc_worker` by `wcObl_XH`. -/
theorem zObl_XH {R : Region} {F : MachineData → Prop} {T : Ty} (hcS : w3.val = .loc cS 0)
    (hik : ∀ y k, Λ.imms (kidC T w0 w1 w2 w3 w4).term y k = none) (hiw : ∀ y k, Λ.imms workerCallH y k = none)
    (hP : ZObl (fun s c fs => PlacedSE Λ lbl s c fs) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m) :
    ZObl (XH Λ lbl) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m where
  hZc i := NodeZA.monoJ (hP.hZc i) fun _ _ hJ _ hp => by
    cases i
    case cb => exact xh_of hp (h3_kidH hik hJ.1 hp)
    case ch => obtain ⟨_, hJ⟩ := hJ; exact xh_of hp (h3_kidH hik hJ.1 hp)
  hzT := ProW.monoJ hP.hzT fun _ _ hJ _ hp => xh_of hp (h3_kidH hik hJ.1 hp)
  hZEt := NodeZA.monoJ hP.hZEt fun _ _ hJ _ hp => xh_of hp (h3_kidH hik hJ.1 hp)
  hZT i := NodeZA.monoJ (hP.hZT i) fun _ _ hJ _ hp => by
    cases i <;> first
      | exact xh_of hp (h3_cS2 hJ)
      | exact xh_of hp (h3_cS2 hJ.1)
  hwc R' F' a b c d e f x29 ra g := wcObl_XH hcS hiw (hP.hwc R' F' a b c d e f x29 ra g)

/-- **The root's immediate table has no entry at `print`'s call** (`zObl_XH`'s `hiw` at the root's table). -/
theorem iH_wcall (Λ0 : Scc.Sem.Layout) (y : String) (k : Nat) :
    Spike.Lib.A64.HelloPh.ImmsH.iH Λ0 workerCallH y k = none := by
  simp [Spike.Lib.A64.HelloPh.ImmsH.iH, Spike.Lib.A64.HelloPh.C0S.immsH, SccCode.helloImms, workerCallH,
    workerRestH, Scc.Sem.SrcSem.setupTerm, SccCode.helloImm_t0, SccCode.helloImm_t1, SccCode.helloImm_t2]

/-- At the root's table both layout premises of `zObl_XH` are met. -/
example (Λ0 : Scc.Sem.Layout) (hi : Λ.imms = Spike.Lib.A64.HelloPh.ImmsH.iH Λ0) {T : Ty} :
    (∀ y k, Λ.imms (kidC T w0 w1 w2 w3 w4).term y k = none) ∧ ∀ y k, Λ.imms workerCallH y k = none :=
  ⟨fun y k => by rw [hi]; exact Spike.Lib.A64.HelloPh.XH.iH_kid Λ0 y k, fun y k => by rw [hi]; exact iH_wcall Λ0 y k⟩

end Spike.Lib.A64.HelloPh.XHNode

/-- info: 'Spike.Lib.A64.HelloPh.XHNode.zObl_XH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XHNode.zObl_XH

/-- info: 'Spike.Lib.A64.HelloPh.XHNode.iH_wcall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XHNode.iH_wcall
