/-
**hello.w on x86-64: main after a refused `clone`** (the spawn's refusal
half, the x86-64 twin of `Spike/Lib/A64HelloSpawnFail.lean`; the parent half
is `Spike/Lib/X64HelloParent.lean`): back from main's `clone`
(`Hello.ThreadsAb.cloneAt`, `.Lwc_main.x25 + 94`) with a refusal in `%rax`
(`ThreadsAb.CloneRef`: `-EAGAIN` or `-ENOMEM`), main runs

    testq %rax, %rax                    -- row (test_ndW): ZF clear
    je .Lwc_main.child.scc_rt_thr_worker                -- not taken
    .x26: movq %rax, -120(%rbp); movq -120(%rbp), %rax; movq $0, %rcx
          cmpq %rcx, %rax; jl .Lwc_main.spawnfail5      -- taken (%rax < 0)
    .spawnfail5: movq $5, %rdi; call scc_rt_abort

in its frame (`Parent.oP`, frame 128), and the call `scc_rt_abort(5)` does
not return (`Abort.Disp.seg_jabort5W`), with the return address
`ThreadsAb.raT lab ".Lwc_main"` that the `call` pushes at `-136`.
`X64WakeSpawnFail`'s blocks and nodes at hello's frame and labels
(`X64HelloParent`'s `tsB`, `jeB`, `x26B`).

- `flB`: `.spawnfail5`'s block.
- `MS cA m`: main's slots of the spawn's words, the box's cell `cA` at `-48`
  and main's `ThreadId` word `m` at `-40` (the fifth argument's slot).
- `fN lab cP cA m`: the nodes (`FN`: `ts`, `je`, `x26`, `fl`).
- `failIn cells`, `hello_failIn`: the blocks and rows at their places.

The segments (`seg_failWS`, `seg_spawnFailWS`) are at the five packet
words' slots, `X64HelloSpawnFailS` (A64: the same split; A64's `fE`,
`seg_failW`, `seg_spawnFailW` at `MS` have no consumer and are not twinned).

**Deviation from the A64 file.** As in `X64WakeSpawnFail`: the result's
test is a row (`testq`) and the `je` a block of its own, so there are four
nodes (`ts`, `je`, `x26`, `fl`; A64: `cb`, `cl`, `fl`); `failIn` is a check
on any cells (A64: an `abbrev` on `helloProg`); the prefix is `.Lwc_main`;
main's slots are `%rbp` offsets (`-48`, `-40`; A64's `-104`, `-112`).
-/
import Spike.Lib.X64HelloParent
import Spike.Lib.X64AbortThreadsW
import Spike.Lib.X64HelloThreadsAb

namespace Spike.Lib.X64.Flow.Worker.Hello.SpawnFail

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker.Hello.Child (x25L)
open Spike.Lib.X64.Flow.Worker.Hello.Parent (oP tsB jeB x26B x26L)
open Spike.Lib.X64.ThreadsAb (CloneRef)
open Scc.Cert.Rt.X64 (blockAt labelGap)

/-! ## The block -/

/-- `.spawnfail5`: the threads code and the call of the dispatcher. -/
def flB : List (Directive × Nat) := (parse("movq $5, %rdi
call scc_rt_abort")).zip [7, 5]

block_spec flB (-136) 16 oP flB

/-- `.spawnfail5`'s label. -/
abbrev flL : Label := ".Lwc_main.spawnfail5"

/-- **The refusal path's blocks and rows in `cells`**: the test and the
`je` at `.x25 + 96`, `+ 99` (`Parent.parentIn`'s), `.x26` twenty-seven cells
(101 bytes) after `.x25`, its block, `.spawnfail5`'s. -/
def failIn (cells : List (Directive × Nat)) : Bool :=
  blockAt cells x25L 25 96 tsB && blockAt cells x25L 26 99 jeB && labelGap cells x25L x26L 27 101 &&
    blockAt cells x26L 0 0 x26B && blockAt cells flL 0 0 flB

theorem hello_failIn : failIn SccCode.helloCells = true := by decide +kernel

/-! ## The nodes -/

/-- The refusal path's internal nodes. -/
inductive FN where
  | ts | je | x26 | fl

/-- **Main's slots of the spawn's words**: the box's cell `cA` at `-48` and
main's `ThreadId` word `m` at `-40` (hello's frame of 128). -/
def MS (cA m : BitVec 64) (σ : AS) : Prop := σ.slot (-48) = cA ∧ σ.slot (-40) = m

variable (lab : Label → Int64) (cP : Ctl) (cA m : BitVec 64)

/-- **The refusal path's nodes**: past the clone (`ts`, `%rax` a refusal),
the `je` (`ZF` clear), `.x26` (`%rax` a refusal), `.spawnfail5` (`fl`); the
source at `cP` and main's slots `MS cA m` throughout. -/
def fN : FN → ND
  | .ts => ⟨lab x25L + 96, oP, fun σ c => c = cP ∧ CloneRef (σ.regs.get64 .rax) ∧ MS cA m σ⟩
  | .je => ⟨lab x25L + 99, oP, fun σ c => c = cP ∧ CloneRef (σ.regs.get64 .rax) ∧ MS cA m σ ∧
      σ.status.zf = false⟩
  | .x26 => ⟨lab x26L, oP, fun σ c => c = cP ∧ CloneRef (σ.regs.get64 .rax) ∧ MS cA m σ⟩
  | .fl => ⟨lab flL, oP, fun σ c => c = cP ∧ MS cA m σ⟩

/-- The nodes' pcs are the threads abort phase's (`Hello.ThreadsAb`'s at hello's
spawn): the test is `pcRet`, the `je` `pcJe`, `.x26` `pcSt`. -/
example : (fN lab cP cA m .ts).pc = Spike.Lib.X64.Hello.ThreadsAb.pcRet lab ".Lwc_main" ".x25" 94 ∧
    (fN lab cP cA m .je).pc = Spike.Lib.X64.Hello.ThreadsAb.pcJe lab ".Lwc_main" ".x25" 94 ∧
    (fN lab cP cA m .x26).pc = Spike.Lib.X64.Hello.ThreadsAb.pcSt lab ".Lwc_main" ".x26" := by
  refine ⟨?_, ?_, rfl⟩ <;> simp only [fN, Spike.Lib.X64.Hello.ThreadsAb.pcRet,
    Spike.Lib.X64.Hello.ThreadsAb.pcJe, Spike.Lib.X64.Hello.ThreadsAb.cloneAt, Int64.add_assoc] <;> rfl

end Spike.Lib.X64.Flow.Worker.Hello.SpawnFail

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.hello_failIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.hello_failIn
