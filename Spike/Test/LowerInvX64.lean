import Scc.Lower.InvX64
import Spike.Lib.Ret0Src

/-!
# x86-64 frame slots and the whole-program lowering on `ret0.w`

`Scc.Lower.InvX64`'s statements instantiated at `ret0.w`: the hypotheses of
`lowerAll_accepted0_x64` hold, the frame of `main` has the one slot `y%0`
at `-8(%rbp)`, and the slot facts and the code of `addChk` and `ret` are
instances there.
-/

namespace Spike.Test.LowerInvX64

open Scc Scc.IR Scc.Lower Scc.Lower.Inv Scc.Lower.InvX64 Scc.Emit.X64
open Spike.Lib.Ret0Src

/-- The lowered `ret0.w` (x86-64). -/
def ret0IR : IR.Program := (Scc.Lower.X64.lowerAll { arch := .x64 } ret0Src).low.ir

/-- `main` in it. -/
def mainF : Func := (ret0IR.funcs.find? (·.name == Names.user "main")).getD (func0 "" {
  insts := [], ret := [], next := 0, marked := [], here := ([], .ret .unit) })

/-- The frame `main` is emitted with. -/
def mainFr : Frame :=
  { frameOf (StackMap.argAreas ret0IR argRegs.length) mainF with maps := ret0IR.growth.isSome }

-- The whole-program statement's hypotheses hold of `ret0.w` (x86-64), and
-- `ret0IR` is the runtime functions, then `func0 main`.
#guard (Scc.Lower.X64.lowerAll? { arch := .x64 } ret0Src).isOk
#guard match rtFuncs .x64 ({ arch := .x64 } : Config).layout ⟨.unit, true⟩ 0 with
  | .ok rt => ret0IR.funcs.map (·.name) == (rt ++ [func0 (Names.user "main") {
      insts := [], ret := [], next := 0, marked := [], here := ([], .ret .unit) }]).map (·.name) &&
      ret0IR.funcs.getLast? == some mainF
  | .error _ => false

-- `main`'s frame: the one slot `y%0`, 16 bytes.
#guard mainFr.slots == [("y%0", 0)] && mainFr.size == 16

theorem mainFr_slots : mainFr.slots = [("y%0", 0)] := by decide +kernel

theorem mainFr_y (s : S) : mainFr.slotOff "y%0" s = .ok (-8, s) :=
  slotOff_find (k := 0) (r' := "y%0") (by rw [mainFr_slots]; rfl) s

-- The generic bounds, at `y%0`.
example : (-8 : Int) ≤ -8 ∧ (-8 : Int) % 8 = 0 ∧ -(-8 : Int) ≤ 8 * (mainFr.slots.length : Int) ∧
    8 * (mainFr.slots.length : Int) +
      8 * (outWords (StackMap.argAreas ret0IR argRegs.length) mainF : Int) ≤ mainFr.size :=
  slotOff_bounds rfl rfl (mainFr_y {})

-- The code of `main`'s `addChk` and `ret`, by the generic lemmas.
example (s : S) : (do ld mainFr (.reg "y%0") .rax : E Unit) s =
    .ok ((), { s with out := .d (i64 (.mov (xr .rax) (om (mem .rbp (-8))))) :: s.out }) :=
  ld_reg (mainFr_y s) .rax

example : emitTerm mainFr (.ret [.reg "y%0"]) =
    (do ld mainFr (.reg "y%0") .rax; epilogue; ins (i64 .ret)) :=
  emitTerm_ret1 _ _

example : emitInst mainFr none (.addChk "y%0" (imm 40) (imm 2)) = (do
    ld mainFr (imm 40) .rax; ld mainFr (imm 2) .rcx
    ins (i64 (.add (xr .rax) (or_ .rcx)))
    ins (i64 (.jcc .c (labelOf mainFr.fn "ovf")))
    st mainFr .rax "y%0") :=
  emitInst_addChk _ _ _ _ _

end Spike.Test.LowerInvX64
