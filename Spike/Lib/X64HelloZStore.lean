/-
**`PassZ` and `ZStoreOk` at hello.w's worker segment's concrete control fact, x86-64** (the twin of
`passZ_ZH`/`zStoreOk_ZH` in `Spike/Lib/A64HelloZ.lean` and `passZ_ZHR`/`zStoreOk_ZHR` in
`Spike/Lib/A64HelloZR.lean`): the premises of `X64HelloPassH` and of `X64HelloW1StoreZ` (`noWrite_IR`,
`noAbW_IR`) at `Z := ZH exe kp` and at `Z := ZHR exe kp`.

- `passZ_ZH`, `passZ_ZHR`: `Z0`'s first part is `helloPass`, `PassZ helloPassT` itself.

- `zStoreOk_ZH`: on no frame `ZH` is off `scc_rt_abort_write`'s system calls (`Z0`) and at no `write` (wake's
  `SysSafe`), so at no `write(1, …)`.
- `zStoreOk_ZHR`: `ZHR` is `ZH` with `RelWS`.

Unlike AArch64, the system call is `syscall`, decoded from `%rax` by the kernel model `Scc.Sem.X64.abi`
(AArch64: `svc`, from `x8`); the proofs are otherwise the same, and live in their own module since `PassZ`
(`X64HelloPassH`) and `ZStoreOk` (`X64HelloW1StoreZ`) import the worker side, above `X64HelloZ`/`X64HelloZR`.
-/
import Spike.Lib.X64HelloZR
import Spike.Lib.X64HelloW1StoreZ
import Spike.Lib.X64HelloPassH

namespace Spike.Lib.X64.Flow.Worker.Hello.Z

open Spike.Lib.X64.Flow.Worker.Hello.Pass (helloPassT)

/-- **`PassZ` at `ZH`**: `Z0`'s first part. -/
theorem passZ_ZH {exe : _root_.Executable} {kp : Nat} : Spike.Lib.X64HelloPassH.PassZ helloPassT (ZH exe kp) :=
  fun _ _ _ h => h.1.1

/-- **`PassZ` at `ZHR`**: from `passZ_ZH`. -/
theorem passZ_ZHR {exe : _root_.Executable} {kp : Nat} : Spike.Lib.X64HelloPassH.PassZ helloPassT (ZHR exe kp) :=
  fun s c fs h => passZ_ZH s c fs h.1

/-- **`ZStoreOk` at `ZH`**: on no frame, off `AbW` (`Z0`) and at no `write` (`SysSafe`). -/
theorem zStoreOk_ZH {ι : Type} {exe : _root_.Executable} {kp : Nat} :
    Spike.Lib.X64HelloW1Store.ZStoreOk exe (fun _ : ι => ZH exe kp) := by
  intro _ s c h _ _
  refine ⟨h.1.2.1 rfl, fun buf n ha hd => ?_⟩
  rcases h.2 rfl ha _ hd with h' | ⟨h', -⟩
  · cases h'
  · exact h' 1 buf n rfl

/-- **`ZStoreOk` at `ZHR`**: from `zStoreOk_ZH`. -/
theorem zStoreOk_ZHR {ι : Type} {exe : _root_.Executable} {kp : Nat} :
    Spike.Lib.X64HelloW1Store.ZStoreOk exe (fun _ : ι => ZHR exe kp) :=
  fun w s c h => zStoreOk_ZH (ι := ι) w s c h.1

/-- Usage: `noWrite_IR`'s and `noAbW_IR`'s premise at the concrete fragment. -/
example (exe : _root_.Executable) (kp : Nat) :
    Spike.Lib.X64HelloW1Store.ZStoreOk exe (fun _ : Unit => ZHR exe kp) := zStoreOk_ZHR

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Z.zStoreOk_ZHR' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms zStoreOk_ZHR

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Z.passZ_ZHR' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms passZ_ZHR

end Spike.Lib.X64.Flow.Worker.Hello.Z
