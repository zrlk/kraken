/-
**The nodes of an `Accepted2` program's run from per-placement segments
inside `W2`** (x86-64; the twin of `Spike/Lib/LowerA64/HN2.lean`): the
fields `hN`, `hT`, `hA` and `hsvc` of `Obl2XE`
(`Spike/Lib/LowerX64/Closed2OfE.lean`) at the multi-level fragment
`AllocReach.IN` from one segment per reachable placement (`SegInvS`) whose
states carry `W2` (`Spike/Lib/LowerX64/SFactsA2.lean`), by
`inst_of_segWAN` (`Spike/Lib/X64SegInstN.lean`) and `sfactsA_of_W2`.

- `nodes2_of_segW2`: `NodesA`, `TakePathS`, `AbortPathS` and `WrInS` at
  `IN ar L0 ls0 inv`, at the owned words `fun s _ => own s`;
- `nodes2_of_segW2_closed`: with `WriteNoPromA` in place of `WrInS`, from
  `write` being a certification dead end (`writeNoPromA_b`), at any write
  tail `Dt`;
- `nodes2_of_segInW2`: each level's segment inside `W2` itself;
- `Svc1S`, `svc1S_of_segInW2`: at every pair of the fragment at an output
  `write(1, …)` the source at `print`'s loop top (`PrintSvc`), from `W2`'s
  `svc1` (`nodes2_of_segInW2`'s last conjunct);
- `emitA_of_svc1S`: the emit rows `EmitA … PrintTop` (`emitA_of_nodes`).
- `site2_ofPlaceOK`: the take site of the parsed output's marks at any
  entry state, `inst_of_segWAN`'s `hμ` (`PhRec.site_ofPlaceOK`).
-/
import Spike.Lib.X64SegInstN
import Spike.Lib.X64WriteDead
import Spike.Lib.LowerX64.SFactsA2
import Spike.Lib.LowerX64.Closed2Of
import Spike.Lib.X64EmitOfNodes

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Ret0 (TakeK)
open Spike.Lib.AllocReach (Reach IN)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {rS : Range} {Tk : State → Prop} {a : Int64}
  {W inv : Lbl → Lsize → FragS isa} {Dt Ab : State → Prop} {ab : Option (State → Prop)}

/-- **The consumer's node obligations from a segment at every reachable
placement inside `W2`**: at each placement `L`, `ls` reachable from `L0`,
`ls0` by allocations, the level `inv L ls` is a segment inside `W L ls`
closed under the take, its rows under the memory side over `IN` (`hseg`);
the take site at `a` (`hμ`); every state of every level in `W2` over `IN`
(`hW2`). -/
theorem nodes2_of_segW2
    (hseg : ∀ L ls, Reach ar L0 ls0 L ls →
      SegInvS (W L ls) (TakeK a rS) p L
        (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 inv) ab L ls) (inv L ls))
    (hμ : μ.site .take = some a.toBitVec.toNat)
    (hW2 : ∀ L ls s c fs, Reach ar L0 ls0 L ls → inv L ls s c fs → W L ls s c fs →
      W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 inv) Dt Ab L ls s c fs) :
    NodesA Λ p μ rd G (fun s _ => own s) ar (IN ar L0 ls0 inv) ab ∧
      TakePathS Λ p μ (IN ar L0 ls0 inv) rS Tk ∧ AbortPathS μ (IN ar L0 ls0 inv) Ab ar.cells ar.ctr ∧
      X64ConsumerA.WrInS (IN ar L0 ls0 inv) Dt :=
  inst_of_segWAN hseg hμ fun L ls s c fs hR hi hw => sfactsA_of_W2 (hW2 L ls s c fs hR hi hw)

/-- **`nodes2_of_segW2` with no promise at a `write`**: `WriteNoPromA` from
`write` being a certification dead end (`writeNoPromA_b`, at `NodesA` and
`TakePathS`), at any write tail `Dt`. -/
theorem nodes2_of_segW2_closed {P : SrcSem.SrcParams}
    (hseg : ∀ L ls, Reach ar L0 ls0 L ls →
      SegInvS (W L ls) (TakeK a rS) p L
        (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 inv) ab L ls) (inv L ls))
    (hμ : μ.site .take = some a.toBitVec.toNat)
    (hW2 : ∀ L ls s c fs, Reach ar L0 ls0 L ls → inv L ls s c fs → W L ls s c fs →
      W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 inv) Dt Ab L ls s c fs) :
    NodesA Λ p μ rd G (fun s _ => own s) ar (IN ar L0 ls0 inv) ab ∧
      TakePathS Λ p μ (IN ar L0 ls0 inv) rS Tk ∧ AbortPathS μ (IN ar L0 ls0 inv) Ab ar.cells ar.ctr ∧
      WriteNoPromA Λ P p G (fun s _ => own s) (IN ar L0 ls0 inv) rS Tk μ ar :=
  have h := nodes2_of_segW2 hseg hμ hW2
  ⟨h.1, h.2.1, h.2.2.1, writeNoPromA_b h.1 h.2.1⟩

/-- **At every pair of `I` at an output `write(1, …)` the source is at
`print`'s loop top** with a byte left (`PrintSvc`): `emitA_of_nodes`'s
`hps`. -/
def Svc1S (I : InvS) : Prop :=
  ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = true → ∀ b n,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 1 b n) → Spike.Lib.PrintSvc.PrintSvc c fs

/-- **`Svc1S` from a segment at every reachable placement inside `W2`**:
`W2`'s `svc1` at each level's states. -/
theorem svc1S_of_segInW2 {K : State → State → Prop} {ms : Lbl → Lsize → List TermRun.Frame → MemSide isa}
    (hseg : ∀ L ls, Reach ar L0 ls0 L ls →
      SegInvS (fun s c fs => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 inv) Dt Ab L ls s c fs) K p L
        (ms L ls) (inv L ls)) :
    Svc1S (IN ar L0 ls0 inv) :=
  fun _ _ _ _ _ ⟨hR, hi⟩ hs b n hd => ((hseg _ _ hR) _ _ _ hi).1.svc1 hs b n hd

/-- **The emit rows at `Top := PrintTop`** from the node obligations with
an abort predicate, `printL` at `printLD` (`hd`) and `Svc1S`
(`emitA_of_nodes`). -/
theorem emitA_of_svc1S {I : InvS} {own' : OwnS} {Ab' : State → Prop}
    (hN : NodesA Λ p μ rd G own' ar I (some Ab')) (hT : TakePathS Λ p μ I rS Tk)
    (hd : p.find? (·.name == "printL") = some PrintSrc.printLD) (h : Svc1S I) :
    EmitA Λ p I Spike.Lib.PrintSvc.PrintTop :=
  emitA_of_nodes hN hT hd h

/-- **`nodes2_of_segW2_closed` with each level's segment inside `W2`
itself** (`W L ls := W2 … L ls`, the form `Spike/Lib/LowerX64/W2Body.lean`'s
block producers give): no separate `hW2`; and `Svc1S` (`svc1S_of_segInW2`). -/
theorem nodes2_of_segInW2 {P : SrcSem.SrcParams}
    (hseg : ∀ L ls, Reach ar L0 ls0 L ls →
      SegInvS (fun s c fs => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 inv) Dt Ab L ls s c fs) (TakeK a rS) p L
        (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 inv) ab L ls) (inv L ls))
    (hμ : μ.site .take = some a.toBitVec.toNat) :
    NodesA Λ p μ rd G (fun s _ => own s) ar (IN ar L0 ls0 inv) ab ∧
      TakePathS Λ p μ (IN ar L0 ls0 inv) rS Tk ∧ AbortPathS μ (IN ar L0 ls0 inv) Ab ar.cells ar.ctr ∧
      WriteNoPromA Λ P p G (fun s _ => own s) (IN ar L0 ls0 inv) rS Tk μ ar ∧ Svc1S (IN ar L0 ls0 inv) :=
  have h := nodes2_of_segW2_closed hseg hμ (fun _ _ _ _ _ _ _ hw => hw)
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, svc1S_of_segInW2 hseg⟩

/-- **The take site of the parsed output's marks** at an output passing
`placeOKAt` and any entry state: its label in the runtime layout
(`PhRec.site_ofPlaceOK`; the parsed target's marks are the record's). -/
theorem site2_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ o = true) (i : Expr → String → Nat → Option Nat) (E : Entry) :
    ((Spike.Lib.X64Consumer.TParE E).marks (asm2 o) Λ).site .take =
      some ((Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i).lab
        Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat :=
  Spike.Lib.X64.PhRec.site_ofPlaceOK h i

/--
info: 'Spike.Lib.LowerX64.nodes2_of_segInW2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodes2_of_segInW2

/--
info: 'Spike.Lib.LowerX64.emitA_of_svc1S' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms emitA_of_svc1S

end Spike.Lib.LowerX64
