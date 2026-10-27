/-
**`SFactsA` at `hello1.w`'s node states, at the levels' shapes**
(`Spike/Lib/A64Hello1SFactsN.lean`): the two forms `hello1_correctKLS_levels`
(`Spike/Test/A64Hello1LevelsA.lean`) asks of `W0` and `W1` at one node, from
the node's `NodeW`.

- `node_w0`: before the allocation, at the static placement and no frame
  (the frames' placement `framesPlaced_nil`).
- `node_w1`: after it, at `upd hello1Λ.static l b` and `updN lsize l n`
  for a fresh `l` (`static_le_upd`), at frames placed under it.
-/
import Spike.Lib.A64Hello1SFactsN
import Spike.Test.A64Hello1CorrectA

namespace Spike.Test.A64Hello1SFactsN

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (FragS EnvSmall)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow.Hello1.Inst
open Spike.Lib.A64.Flow.Hello1.SFactsN
open Spike.Lib (Region)
open Spike.Lib.A64.Flow (NodeW At ND)
open Spike.Lib.A64.Flow.Hello1.Mem (hello1Exe hello1End)
open Spike.Test.A64Hello1Load (hello1M0)
open Spike.Test.A64ArenaHello1 (ar)
open Spike.Test.A64Hello1CorrectA (Ih)
open SccCode (hello1Λ hello1Prog hello1Asm)

variable {p : Prog} {rd : TermRun.Word → Prop} {Fix : List (Nat × Val)} {lsize : Lsize} {rS : Range}
  {inv0 : FragS isaLSE2} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt Ab : State → Prop}
  {R : Region} {F : MachineData → Prop} {n : ND}

/-- **`W0`'s form at a node** before the allocation, no frame. -/
theorem node_w0 (hpa : Scc.Sem.A64.textProgram hello1Asm = .ok hello1Prog)
    (hN : NodeW (Wr rS) (Kr rS) hello1Exe hello1End R F n)
    (hab : ∀ s c, At hello1Exe hello1End R F n s c → AbSt μ0 Ab s)
    (hrun : ∀ s c, At hello1Exe hello1End R F n s c → RunOk p c [])
    (hwr : ∀ s c, At hello1Exe hello1End R F n s c → NoArenaWr ar s) :
    ∀ s c fs, (At hello1Exe hello1End R F n).at [] s c fs →
      SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd (FixG Fix hello1M0) (fun s _ => own s) rS Tk ar
        (Ih lsize inv0 inv1) hello1Λ.static lsize s c fs Dt Ab :=
  sfactsA_node hpa hN (fun _ _ h => h) (fun _ _ _ => framesPlaced_nil) (fun _ h => by cases h) hab hrun hwr

/-- **`W1`'s form at a node** after the allocation of the fresh `l` at `b`
of `n` words, at frames `fs` placed under the new placement. -/
theorem node_w1 (hpa : Scc.Sem.A64.textProgram hello1Asm = .ok hello1Prog)
    (hN : NodeW (Wr rS) (Kr rS) hello1Exe hello1End R F n) {l : WeakMem.AllocLabel} {b k : Nat}
    {fs : List TermRun.Frame} (hl : hello1Λ.static l = none)
    (hfp : ∀ s c, At hello1Exe hello1End R F n s c → FramesPlaced hello1Λ (upd hello1Λ.static l b) s fs)
    (hes : ∀ f ∈ fs, EnvSmall f.env)
    (hab : ∀ s c, At hello1Exe hello1End R F n s c → AbSt μ0 Ab s)
    (hrun : ∀ s c, At hello1Exe hello1End R F n s c → RunOk p c fs)
    (hwr : ∀ s c, At hello1Exe hello1End R F n s c → NoArenaWr ar s) :
    ∀ s c fs', (At hello1Exe hello1End R F n).at fs s c fs' →
      SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd (FixG Fix hello1M0) (fun s _ => own s) rS Tk ar
        (Ih lsize inv0 inv1) (upd hello1Λ.static l b) (updN lsize l k) s c fs' Dt Ab :=
  sfactsA_node hpa hN (static_le_upd hl) hfp hes hab hrun hwr

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.A64.Flow.Hello1.SFactsN.sfactsA_of'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sfactsA_of'

/--
info: 'Spike.Lib.A64.Flow.Hello1.SFactsN.sfactsA_node'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sfactsA_node'

/--
info: 'Spike.Lib.A64.Flow.Hello1.SFactsN.RunOk.ofGood1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RunOk.ofGood1

/--
info: 'Spike.Lib.A64.Flow.Hello1.SFactsN.runOk_hello1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms runOk_hello1

/--
info: 'Spike.Test.A64Hello1SFactsN.node_w0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms node_w0

/--
info: 'Spike.Test.A64Hello1SFactsN.node_w1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms node_w1

/--
info: 'Spike.Lib.A64.Flow.Hello1.SFactsN.runOk_ho' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms runOk_ho

/--
info: 'Spike.Lib.A64.Flow.Hello1.SFactsN.runOk_hello1o' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms runOk_hello1o

end Spike.Test.A64Hello1SFactsN
