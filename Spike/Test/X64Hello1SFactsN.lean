/-
**`SFactsA` at `hello1.w`'s node states on x86-64, at the levels' shapes**
(`Spike/Lib/X64Hello1SFactsN.lean`): the two forms `hello1_correctKLS_levels`
(`Spike/Test/X64Hello1LevelsA.lean`) asks of `W0` and `W1` at one node, from
the node's `NodeW`; and the axioms of the library's lemmas.

- `node_w0`: before the allocation, at the static placement and no frame
  (the frames' placement `framesPlaced_nil`).
- `node_w1`: after it, at `upd hello1Λ.static l b` and `updN lsize l n`
  for a fresh `l` (`static_le_upd`), at frames placed under it.
-/
import Spike.Lib.X64Hello1SFactsN
import Spike.Test.X64Hello1CorrectA
import Spike.Lib.X64Hello1SetupPre

namespace Spike.Test.X64Hello1SFactsN

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (FragS EnvSmall Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (At NodeW ND)
open Spike.Lib.X64.Flow.Hello1.Inst (Wr Kr μ0 own Tk)
open Spike.Lib.X64.Flow.Hello1.Mem (hello1Exe hello1End)
open Spike.Lib.X64.Flow.Hello1.SFactsN
open Spike.Test.X64Hello1Load (hello1M0)
open Spike.Test.X64ArenaHello1 (ar)
open Spike.Test.X64Hello1CorrectA (Ih)
open SccCode (hello1Asm hello1Λ hello1Cells)

variable {p : Prog} {rd : TermRun.Word → Prop} {Fix : List (Nat × Val)} {lsize : Lsize} {rS : Range}
  {inv0 : FragS isa} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt Ab : State → Prop}
  {R : Region} {F : MachineData → Prop} {n : ND}

/-- **`W0`'s form at a node** before the allocation, no frame. -/
theorem node_w0 (hpa : Scc.Sem.X64.cellsOf hello1Asm = some hello1Cells)
    (hN : NodeW (Wr rS) (Kr rS) hello1Exe hello1End R F n)
    (hab : ∀ s c, At hello1Exe hello1End R F n s c → AbSt μ0 Ab s)
    (hrun : ∀ s c, At hello1Exe hello1End R F n s c → RunOk p c [])
    (hwr : ∀ s c, At hello1Exe hello1End R F n s c → NoArenaWr ar s) :
    ∀ s c fs, (At hello1Exe hello1End R F n).at [] s c fs →
      SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd (FixG Fix hello1M0) (fun s _ => own s) rS Tk ar
        (Ih lsize inv0 inv1) hello1Λ.static lsize s c fs Dt Ab :=
  sfactsA_node hpa hN (fun _ _ h => h) (fun _ _ _ => framesPlaced_nil) (fun _ h => by cases h) hab hrun hwr

/-- **`W1`'s form at a node** after the allocation of the fresh `l` at `b`
of `k` words, at frames `fs` placed under the new placement. -/
theorem node_w1 (hpa : Scc.Sem.X64.cellsOf hello1Asm = some hello1Cells)
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

/-- **`RunOk` at a node of `rodata`'s body under the setup block's frame**
(`runOk_of_term`): the term and the frame's body, the start's continuation,
among `hello1Terms`. -/
example {env : TermRun.Env} {e : Expr} (he : e = .let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a")))
    {c : Spike.Lib.Ctl} (hc : c.term = Spike.Lib.Hello1RodataSrc.eO0) :
    RunOk Spike.Lib.Hello1Src.hello1Src c [Spike.Lib.X64.Flow.Hello1.setupFrame e env] :=
  runOk_of_term (by rw [hc]; simp [Spike.Lib.Hello1Runs.hello1Terms])
    (by subst he; simp [Spike.Lib.X64.Flow.Hello1.setupFrame, Spike.Lib.Hello1Runs.hello1Terms])

-- No axioms beyond Lean's.
/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.RunOk.run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RunOk.run

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.RunOk.ofGood1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RunOk.ofGood1

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.wrOkA_of_noArenaWr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms wrOkA_of_noArenaWr

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.noArenaWr_of_noWr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noArenaWr_of_noWr

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.noArenaWr_store' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noArenaWr_store

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.locRep_mono' does not depend on any axioms
-/
#guard_msgs in
#print axioms locRep_mono

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.wordPlaceRep_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms wordPlaceRep_mono

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.Placed.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Placed.mono

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.FramesPlaced.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FramesPlaced.mono

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.framesPlaced_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms framesPlaced_nil

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.static_le_upd' does not depend on any axioms
-/
#guard_msgs in
#print axioms static_le_upd

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.sfactsA_of'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sfactsA_of'

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.sfactsA_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sfactsA_of

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.sfactsA_wr'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sfactsA_wr'

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.sfactsA_wr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sfactsA_wr

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.sfactsA_node'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sfactsA_node'

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.sfactsA_node' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sfactsA_node

/--
info: 'Spike.Test.X64Hello1SFactsN.node_w0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms node_w0

/--
info: 'Spike.Test.X64Hello1SFactsN.node_w1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms node_w1

/--
info: 'Spike.Lib.Hello1Runs.good1H_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.Hello1Runs.good1H_run

/--
info: 'Spike.Lib.Hello1Runs.Good1H.newBuf_ty' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Spike.Lib.Hello1Runs.Good1H.newBuf_ty

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.runOk_hello1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms runOk_hello1

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.runOk_of_term' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms runOk_of_term

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.runOk_ho' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms runOk_ho

/--
info: 'Spike.Lib.X64.Flow.Hello1.SFactsN.runOk_hello1o' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms runOk_hello1o

end Spike.Test.X64Hello1SFactsN
