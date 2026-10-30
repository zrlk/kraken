import Scc.Lower.InvBodyX64
import Spike.Lib.Ret0Src

/-!
# The x86-64 frame of `ret0.w`'s body, by the per-step invariants

`Scc.Lower.InvBodyX64`'s statements instantiated at `ret0.w`'s code block
`main` (the x86-64 twin of `Spike/Test/LowerInvBody.lean`): with any
argument areas, the registers with a slot are the registers `main` writes,
there is no outgoing area, the frame is its slots rounded up to 16 bytes,
and `BodyInv` holds at the start of the body. Each is an application of the
generic theorem to the closed form; nothing decides over the whole program.
-/

namespace Spike.Test.LowerInvBodyX64

open Scc Scc.IR Scc.Lower Scc.Lower.Inv Scc.Lower.InvX64 Scc.Emit.X64
open Spike.Lib.Ret0Src

/-- `ret0.w`'s code block. -/
def main0 : CoreTerm.Decl :=
  { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int, body := ret0Body }

theorem ret0Src_eq : ret0Src = [main0] := rfl

theorem main0_accepted : Accepted0 [main0] = true := by decide

/-- The closed form of `main`'s body. -/
def ret0Res : Res :=
  { insts := [.addChk "y%0" (imm 40) (imm 2)], ret := [.reg "y%0"], next := 1,
    marked := ["y%0"],
    here := ([("y", .int, [.reg "y%0"]), ("x", .intS (.lit 40), [imm 40]), ("u", .unit, [])],
      .ret (.var "y")) }

theorem ret0_lower0 : lower0 [(main0.arg, .unit, [])] 0 main0.body = some ret0Res := rfl

/-- `main`'s function. -/
abbrev mainF : Func := func0 (Names.user "main") ret0Res

example (areas : List (Sym × Nat)) (x : IR.Reg) :
    x ∈ slotRegs (frameOf areas mainF) ↔ x ∈ defsOf ret0Res.insts :=
  mem_slots_func0 areas _ ret0_lower0 x

example (areas : List (Sym × Nat)) : (frameOf areas mainF).slots.length ≤ 1 :=
  slots_length_func0 areas _ ret0_lower0

example (areas : List (Sym × Nat)) : outWords areas mainF = 0 :=
  outWords_func0 areas _ (lower0_insts_addChk _ _ _ _ ret0_lower0).1

example (areas : List (Sym × Nat)) : (frameOf areas mainF).size % 16 = 0 :=
  (frameOf_size_func0 areas _ (lower0_insts_addChk _ _ _ _ ret0_lower0).1).2

example (areas : List (Sym × Nat)) :
    BodyInv (slotRegs (frameOf areas mainF)) 0 [(main0.arg, .unit, [])] :=
  (bodyInv_func0_x64 areas _ ret0_lower0).1

-- The whole-program statement at `ret0.w` (x86-64): whenever the lowering
-- and emission succeed, `main`'s frame has the invariants.
example (em : Scc.Lower.X64.Emitted) (h : Scc.Lower.X64.lowerAll? { arch := .x64 } ret0Src = .ok em) :
    ∃ rt, rtFuncs .x64 ({ arch := .x64 } : Config).layout ⟨.unit, true⟩ 0 = .ok rt ∧
      let fr : Frame := { frameOf (StackMap.argAreas (progOf ({ arch := .x64 } : Config).layout rt
        [mainF]) argRegs.length) mainF with
        maps := (progOf ({ arch := .x64 } : Config).layout rt [mainF]).growth.isSome }
      fr.size % 16 = 0 ∧ BodyInv (slotRegs fr) 0 [(main0.arg, .unit, [])] := by
  rw [ret0Src_eq] at h
  obtain ⟨r, rt, hr, hrt, -, hc⟩ := main_inv_x64 { arch := .x64 } main0_accepted h
  rw [ret0_lower0] at hr
  cases hr
  obtain ⟨-, -, hm, -, -, -, -, -, hI, -⟩ := hc
  exact ⟨rt, hrt, hm, hI⟩

end Spike.Test.LowerInvBodyX64
