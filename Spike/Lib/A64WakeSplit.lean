/-
**wake.w's spawned child, at the source** (`hsplit` of
`Spike.Lib.A64.Flow.Worker.Wake.seg_thrWorker`): the spawn leaves the child
at `tail worker [] (var "a") []` on the argument's two words
(`WeakCore`'s `spawnKid`); its tail call enters `worker`'s body
(`localStep_tailCall`), whose `split` binds `c` and `j` to the first and
second word (`Spike.Lib.Form.localStep_split`): the control `wc1` at the
`store rel c 1`.

- `workerBody`: `worker`'s body in `Spike.Lib.WakeT1.wakeSrc` (`rfl`).
- `wc1 T w1 w2 ws`: the control after the `split`.
- `worker_split`: the body's `split` (the `hsplit` of `seg_thrWorker`).
- `kid_split`: the child's tail call and the `split`.
- `wakeSrc_worker`: `worker` in `wakeSrc` has that body and argument.
-/
import Spike.Lib.A64WakeParent
import Spike.Lib.Form
import Spike.Lib.WakeA64

namespace Spike.Lib.A64.Flow.Worker.Wake.Split

open CoreLang CoreTerm
open Spike.Lib.A64.Flow.Worker.Wake.Parent (localStep_tailCall)

/-- `worker`'s argument type: the cell and main's `ThreadId`. -/
abbrev workerTy : Ty := .prod (.ptr .pub .int) .tid

/-- `worker`'s body after its `split`. -/
def workerRest : Expr :=
  .let_ "d" (.store true (.var "c") (.lit 1) none) (.let_ "w" (.ext .unpark (.var "j")) (.ret .unit))

/-- `worker`'s body. -/
def workerBody : Expr := .split (.var "a") "c" "j" workerRest

/-- **The control at the `store rel c 1`**: `j`, `c` bound to the second and
first word, `a` (at type `T`) to both. -/
def wc1 (T : Ty) (w1 w2 : TermRun.Word) : Spike.Lib.Ctl :=
  ⟨workerRest, [("j", .tid, [w2]), ("c", .ptr .pub .int, [w1]), ("a", T, [w1, w2])], none⟩

theorem close_workerTy : TermRun.close [] workerTy = workerTy := rfl

/-- **The body's `split`**: on `a` at `workerTy` bound to two words, `c`
gets the first and `j` the second. -/
theorem worker_split {p : Prog} (w1 w2 : TermRun.Word) :
    LocalStep p ⟨workerBody, [("a", workerTy, [w1, w2])], none⟩ (wc1 workerTy w1 w2) :=
  Spike.Lib.Form.localStep_split (c := ⟨workerBody, [("a", workerTy, [w1, w2])], none⟩) (us := [.one]) rfl rfl rfl

/-- **The child's tail call and `split`**: from the spawn's `tail worker []
(var "a") []` on two words, to `wc1`. -/
theorem kid_split {p : Prog} {d : Decl} (hd : p.find? (·.name == "worker") = some d)
    (hb : d.body = workerBody) (ha : d.arg = "a") (hty : d.argTy = workerTy) {T : Ty}
    (w1 w2 : TermRun.Word) :
    LocalRun p ⟨.tail "worker" [] (.var "a") [], [("a", T, [w1, w2])], none⟩ (wc1 workerTy w1 w2) := by
  refine .step (localStep_tailCall rfl hd rfl) ?_
  rw [hb, ha, hty, close_workerTy]
  exact .single (worker_split w1 w2)

/-- **`worker` in wake.w** has the body `workerBody` on `a : workerTy`. -/
theorem wakeSrc_worker : ∃ d, Spike.Lib.WakeT1.wakeSrc.find? (·.name == "worker") = some d ∧
    d.body = workerBody ∧ d.arg = "a" ∧ d.argTy = workerTy :=
  ⟨_, rfl, rfl, rfl, rfl⟩

end Spike.Lib.A64.Flow.Worker.Wake.Split
