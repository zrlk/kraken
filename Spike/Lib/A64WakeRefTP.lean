/-
**The threads abort path's node obligations as one structure** (AArch64):
`TPathW W K exe endPc R F c0 ra` lists the dispatcher's blocks at code 5 and
the threads stub's nodes, the `write` call's node `ssvc` among them (the
shape of `WakePh.AbPT`/`AbAgree` at any fragment), so that per-component
facts combine node by node before `Abort.Disp.StubTW` is built from the code
(`StubW.stubTW_of_code`).

- `TPathW`: the obligations; `TPathW.and`: two into one (the first's move).
- `TPathW.ofStub`: from `StubTW`'s nodes and the `write` call's node.
- `TPathW.ofAbPT`, `TPathW.ofAgree`: `AbPT`'s and `AbAgree`'s nodes.
- `TPathW.stub`: `StubTW` from the obligations and the abort code.
-/
import Spike.Lib.A64StubTAC
import Spike.Lib.A64WakeOwnGAbT

namespace Spike.Lib.WakeRefTP

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (Region)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.Abort (NT)
open Spike.Lib.A64.Abort.Disp (DN)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {ra : BitVec 64}

set_option hygiene false in
/-- The labels of the executable. -/
local notation "lb" => (_root_.Executable.labels exe).label

/-- **The threads abort path's node obligations** inside `W` under `K`. -/
structure TPathW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 : Ctl) (ra : BitVec 64) : Prop where
  de : BlkW W K exe endPc R F (DN.nd5 lb c0 ra .e) Spike.Lib.A64.Abort.Disp.d0
  dt1 : BlkW W K exe endPc R F (DN.nd5 lb c0 ra .t1) Spike.Lib.A64.Abort.Disp.t1
  dj1 : BlkW W K exe endPc R F (DN.nd5 lb c0 ra .j1) Spike.Lib.A64.Abort.Disp.j1
  dt2 : BlkW W K exe endPc R F (DN.nd5 lb c0 ra .t2) Spike.Lib.A64.Abort.Disp.t2
  dj2 : BlkW W K exe endPc R F (DN.nd5 lb c0 ra .j2) Spike.Lib.A64.Abort.Disp.j2
  dt3 : BlkW W K exe endPc R F (DN.nd5 lb c0 ra .t3) Spike.Lib.A64.Abort.Disp.t3
  dj3 : BlkW W K exe endPc R F (DN.nd5 lb c0 ra .j3) Spike.Lib.A64.Abort.Disp.j3
  dt4 : BlkW W K exe endPc R F (DN.nd5 lb c0 ra .t4) Spike.Lib.A64.Abort.Disp.t4
  dj4 : BlkW W K exe endPc R F (DN.nd5 lb c0 ra .j4) Spike.Lib.A64.Abort.Disp.j4
  dt5 : BlkW W K exe endPc R F (DN.nd5 lb c0 ra .t5) Spike.Lib.A64.Abort.Disp.t5
  dg5 : BlkW W K exe endPc R F (DN.nd5 lb c0 ra .g5) Spike.Lib.A64.Abort.Disp.g5
  se : BlkW W K exe endPc R F (NT lb Spike.Lib.A64.Abort.threads c0 ra .e) Spike.Lib.A64.Abort.b0
  sn1 : NodeW W K exe endPc R F (NT lb Spike.Lib.A64.Abort.threads c0 ra .n1)
  sn1b : NodeW W K exe endPc R F (NT lb Spike.Lib.A64.Abort.threads c0 ra .n1b)
  sn2 : BlkW W K exe endPc R F (NT lb Spike.Lib.A64.Abort.threads c0 ra .n2) Spike.Lib.A64.Abort.b1Threads
  ssvc : NodeW W K exe endPc R F (NT lb Spike.Lib.A64.Abort.threads c0 ra .svc)
  sn5 : BlkW W K exe endPc R F (NT lb Spike.Lib.A64.Abort.threads c0 ra .n5) Spike.Lib.A64.Abort.b2
  sex : NodeW W K exe endPc R F (NT lb Spike.Lib.A64.Abort.threads c0 ra .ex)

/-- **Two path obligations into one**: one inside `W₁` under `K`, one inside
`W₂` under any move, `W₁ ∧ W₂` inside `W`. -/
theorem TPathW.and {W W₁ W₂ : Frag isaLSE2} {K K₂ : State → State → Prop} (h₁ : TPathW W₁ K exe endPc R F c0 ra)
    (h₂ : TPathW W₂ K₂ exe endPc R F c0 ra) (hw : ∀ s c, W₁ s c → W₂ s c → W s c) :
    TPathW W K exe endPc R F c0 ra := by
  have hb : ∀ {n : ND} {blk : List Directive}, BlkW W₁ K exe endPc R F n blk →
      BlkW W₂ K₂ exe endPc R F n blk → BlkW W K exe endPc R F n blk :=
    fun h₁ h₂ s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
      ⟨hw _ c (h₁ s σ c he hn hd hp hA hF hJ k hk m hA' hD).1 (h₂ s σ c he hn hd hp hA hF hJ k hk m hA' hD).1,
        (h₁ s σ c he hn hd hp hA hF hJ k hk m hA' hD).2⟩
  have hn : ∀ {n : ND}, NodeW W₁ K exe endPc R F n → NodeW W₂ K₂ exe endPc R F n → NodeW W K exe endPc R F n :=
    fun h₁ h₂ s c hA => ⟨hw s c (h₁ s c hA).1 (h₂ s c hA).1, (h₁ s c hA).2⟩
  exact ⟨hb h₁.de h₂.de, hb h₁.dt1 h₂.dt1, hb h₁.dj1 h₂.dj1, hb h₁.dt2 h₂.dt2, hb h₁.dj2 h₂.dj2,
    hb h₁.dt3 h₂.dt3, hb h₁.dj3 h₂.dj3, hb h₁.dt4 h₂.dt4, hb h₁.dj4 h₂.dj4, hb h₁.dt5 h₂.dt5,
    hb h₁.dg5 h₂.dg5, hb h₁.se h₂.se, hn h₁.sn1 h₂.sn1, hn h₁.sn1b h₂.sn1b, hb h₁.sn2 h₂.sn2,
    hn h₁.ssvc h₂.ssvc, hb h₁.sn5 h₂.sn5, hn h₁.sex h₂.sex⟩

/-- **From `StubTW`'s nodes** and the `write` call's node (`hsvc`). -/
theorem TPathW.ofStub {W : Frag isaLSE2} {K : State → State → Prop} {p : CoreTerm.Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    (h : Spike.Lib.A64.Abort.Disp.StubTW W K p lbl ms exe endPc R F c0 ra)
    (hsvc : NodeW W K exe endPc R F (NT lb Spike.Lib.A64.Abort.threads c0 ra .svc)) : TPathW W K exe endPc R F c0 ra :=
  ⟨h.de, h.dt1, h.dj1, h.dt2, h.dj2, h.dt3, h.dj3, h.dt4, h.dj4, h.dt5, h.dg5, h.se, h.sn1, h.sn1b, h.sn2,
    hsvc, h.sn5, h.sex⟩

/-- **`AbPT`'s nodes.** -/
theorem TPathW.ofAbPT {L : Spike.Lib.A64.Rt.RuntimeLayout} {μ : Scc.Sem.Marks}
    (h : Spike.Lib.A64.WakePh.AbPT L μ endPc R F c0 ra) :
    TPathW (Spike.Lib.A64.WakePh.AbW L R ra μ) (fun _ _ => False) L.exe endPc R F c0 ra :=
  ⟨h.de, h.dt1, h.dj1, h.dt2, h.dj2, h.dt3, h.dj3, h.dt4, h.dj4, h.dt5, h.dg5, h.se, h.sn1, h.sn1b, h.sn2,
    h.ssvc, h.sn5, h.sex⟩

/-- **`AbAgree`'s nodes.** -/
theorem TPathW.ofAgree {L : Spike.Lib.A64.Rt.RuntimeLayout} {a : BitVec 64} {own : State → List (Loc × Val)}
    {μ : Scc.Sem.Marks} (h : Spike.Lib.A64.WakePh.AbAgree L a own μ endPc R F c0 ra) :
    TPathW (Spike.Lib.A64.WakePh.AgW L a own μ) (fun _ _ => False) L.exe endPc R F c0 ra :=
  ⟨h.de, h.dt1, h.dj1, h.dt2, h.dj2, h.dt3, h.dj3, h.dt4, h.dj4, h.dt5, h.dg5, h.se, h.sn1, h.sn1b, h.sn2,
    h.ssvc, h.sn5, h.sex⟩

/-- **`StubTW` from the obligations** and the abort code (`stubTW_of_code`),
the exit call at an abort site of the memory side (`hab`). -/
theorem TPathW.stub [Kraken.Executable.ValidLayout exe] {W : Frag isaLSE2} {K : State → State → Prop} {p : CoreTerm.Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {prog : List Directive} {kp : Nat}
    (h : TPathW W K exe endPc R F c0 ra) (hp : Scc.Cert.Rt.A64.Lays exe prog kp)
    (hend : endPc = Scc.Cert.Rt.A64.endOf exe prog kp) (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : Spike.Lib.A64.Flow.FStable R F)
    (hab : ∀ s c, At exe endPc R F (NT lb Spike.Lib.A64.Abort.threads c0 ra .ex) s c → ms.abortAt s) :
    Spike.Lib.A64.Abort.Disp.StubTW W K p lbl ms exe endPc R F c0 ra :=
  Spike.Lib.A64.StubW.stubTW_of_code hp hend hprog hK hF h.de h.dt1 h.dj1 h.dt2 h.dj2 h.dt3 h.dj3 h.dt4 h.dj4
    h.dt5 h.dg5 h.se h.sn1 h.sn1b h.sn2 h.ssvc h.sn5 h.sex hab

end Spike.Lib.WakeRefTP

/-- info: 'Spike.Lib.WakeRefTP.TPathW.and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRefTP.TPathW.and

/-- info: 'Spike.Lib.WakeRefTP.TPathW.stub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRefTP.TPathW.stub
