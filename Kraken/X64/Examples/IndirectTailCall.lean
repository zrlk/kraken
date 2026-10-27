module

public import Kraken.StateCfg
import Kraken.X64.Parser

/-!
# An indirect tail call through a code pointer in memory

`invoke` calls the function an object points to, as a tail call:

```c
struct obj { long data; long (*fn)(struct obj *); };
long invoke(struct obj *o) { return o->fn(o); }
```

```
invoke:
    jmp     qword ptr [rdi + 8]       ; o->fn, at offset 8
```

`invoke_spec` is higher-order: it is stated over any code address `f` that
runs to its return address with some postcondition (`RunsTo`, a statement
about the machine's steps). If the object's pointer is `f` and `f`'s
precondition holds, then `invoke` runs to the return address with `f`'s
postcondition. `handler` is one such `f` (`mov eax, 42; ret`), and
`invoke_handler` instantiates `invoke_spec` with it.

## Findings

* `jmp_mem_spec` asks that the 8 bytes be readable and exits at the address
  they hold: where control lands is the caller's business. The body's triple
  (`invoke_jumps`) says just that: `invoke` exits at `f`, in its entry state.
* A tail call reaches `ra` through `f`, so `invoke_spec` chains the readback of
  `invoke`'s triple to the machine (`Program.step1_of_wp`) with `f`'s run. The
  cfg rule reads a jump to `invoke`'s own label as a loop, so the triple
  assumes `f ≠ label "invoke"`; when the object points to `invoke` itself,
  `invoke_spec` is `f`'s run.
* `handler`'s triple is in the procedure-spec form (entered at `s.pushRa ra`);
  `handler_runsTo` reads it back to a `RunsTo` at `label "handler"`.
* The pointer is stated as `fnPtr t = some f`: the 8 bytes at `rdi + 8`,
  decoded as an address, in the style of `MachineData.retAddr`. The caller,
  not the program, establishes it.
-/

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Kraken.Examples.IndirectTailCall

def invoke_body : Program := parse("
invoke:
  jmp *8(%rdi)
")

def handler_body : Program := parse("
handler:
  movl $42, %eax
  ret
")

/-- The code pointer of the object `rdi` points to: the 8 bytes at offset 8,
read as an address. -/
abbrev fnPtr (t : MachineData) : Option Int64 :=
  (Mem.loadInt t.dmem (t.regs.get64 .rdi + 8) 8).map (fun v => Int64.ofBitVec (BitVec.ofInt 64 v))

/-- The code at `entry`, entered in a state `t` with return address `ra` and
`Pre x ra t`, runs to `ra` with `Post x ra t`. -/
def RunsTo [Host] (entry : Int64) {α : Type} (Pre : α → Int64 → MachineData → Prop)
    (Post : α → Int64 → MachineData → MachineData → Prop) : Prop :=
  ∀ x ra t, Pre x ra t →
    Eventually (step1 Host.exe) (fun u => u.pc = ra ∧ Post x ra t u.data) ⟨t, entry⟩

theorem get!_fnPtr {t : MachineData} {f : Int64} (h : fnPtr t = some f) :
    (Mem.loadInt t.dmem (t.regs.get64 .rdi + 8) 8).isSome = true
      ∧ Int64.ofBitVec (BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.get64 .rdi + 8) 8).get!) = f := by
  cases hl : Mem.loadInt t.dmem (t.regs.get64 .rdi + 8) 8 with
  | none => unfold fnPtr at h; rw [hl] at h; simp at h
  | some v =>
    unfold fnPtr at h; rw [hl, Option.map_some, Option.some.injEq] at h
    simp [h]

/-- `invoke` exits at the object's code pointer, in its entry state. -/
theorem invoke_jumps [Host] [FunDecls] (t₀ : MachineData) (f : Int64) (hne : f ≠ label "invoke") :
    ⦃ fun t => t = t₀ ∧ fnPtr t₀ = some f ⦄
      invoke_body
    ⦃ (fun _ _ => False); fun a t => a = f ∧ t = t₀ ⦄ := by
  refine ⟨fun t ⟨h₀, hp⟩ => ?_⟩
  subst h₀
  obtain ⟨hsome, hf⟩ := get!_fnPtr hp
  refine Program.WP.cfg (fun
      | .entry, u | .label "invoke", u => u = t
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

/-- Whatever `f` does, `invoke` does, given that the object points to `f`. -/
theorem invoke_spec [Host] [FunDecls] [he : Embeds invoke_body] {α : Type}
    {Pre : α → Int64 → MachineData → Prop} {Post : α → Int64 → MachineData → MachineData → Prop}
    {f : Int64} (hf : RunsTo f Pre Post) :
    RunsTo (label "invoke") (fun x ra t => fnPtr t = some f ∧ Pre x ra t) Post := by
  rintro x ra t ⟨hp, hpre⟩
  by_cases hne : f = label "invoke"
  · exact hne ▸ hf x ra t hpre
  have hstart : label "invoke" = he.embedding.startAddr := by
    rw [Host.label_eq he.embedding.isInfixAt (i := 0) rfl]; rfl
  rw [hstart]
  refine eventually_trans _ _ _ _
    (Program.step1_of_wp (post := fun u => u.pc = f ∧ u.data = t)
      ((invoke_jumps t f hne).1 t ⟨rfl, hp⟩) (fun _ _ h => h.elim) (fun _ h => h)) ?_
  rintro ⟨u, pc⟩ ⟨hpc, hu⟩
  dsimp only at hpc hu
  subst hpc hu
  exact hf x ra u hpre

/-- `handler` returns 42. -/
theorem handler_spec [Host] [FunDecls] (s : MachineData) (ra : Int64) :
    ⦃ fun t => t = s.pushRa ra ⦄
      handler_body
    ⦃ (fun _ _ => False); fun a t => a = ra
      ∧ t.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp + 8 ∧ t.dmem = (s.pushRa ra).dmem
      ∧ t.regs.get64 .rax = 42 ⦄ := by
  refine ⟨fun t₀ h₀ => ?_⟩
  subst h₀
  refine Program.WP.cfg (fun
      | .entry, t | .label "handler", t => t = s.pushRa ra
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

/-- `handler`'s triple, read back to the machine. -/
theorem handler_runsTo [Host] [FunDecls] [he : Embeds handler_body] :
    RunsTo (label "handler") (α := Unit)
      (fun _ ra t => ∃ s : MachineData, t = s.pushRa ra)
      (fun _ _ t u => u.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ u.dmem = t.dmem
        ∧ u.regs.get64 .rax = 42) := by
  rintro _ ra t ⟨s, rfl⟩
  have hstart : label "handler" = he.embedding.startAddr := by
    rw [Host.label_eq he.embedding.isInfixAt (i := 0) rfl]; rfl
  rw [hstart]
  exact Program.step1_of_wp ((handler_spec s ra).1 _ rfl) (fun _ _ h => h.elim)
    (fun _ ⟨hpc, h⟩ => ⟨hpc, h⟩)

/-- `invoke` on an object that points to `handler` returns 42. -/
theorem invoke_handler [Host] [FunDecls] [Embeds invoke_body] [Embeds handler_body] :
    RunsTo (label "invoke") (α := Unit)
      (fun _ ra t => fnPtr t = some (label "handler") ∧ ∃ s : MachineData, t = s.pushRa ra)
      (fun _ _ t u => u.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ u.dmem = t.dmem
        ∧ u.regs.get64 .rax = 42) :=
  invoke_spec handler_runsTo

end Kraken.Examples.IndirectTailCall
