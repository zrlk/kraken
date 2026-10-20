/-
**`bl` … `ret` and `blr` on AArch64
`isaLSE2`** (point 4 of the draft calling convention).

- `exec_bl`, `exec_blr`, `exec_ret`, `exec_br` (`Lower/EventsA64.lean`): each
  is a no-event step (`.done`), so on the fuel-free machine a source stutter
  (`Lower.instrSemInf_done_stutter`); `bl`/`blr` write the return address
  `retAddr st sz` (the bits of `pc + sz`) to `X30`; `blr Xn` jumps to the
  address `Xn` held before the call.
- `x30_after_bl`: after `bl`/`blr`, `X30` holds `retAddr`.
- `ret_to`: `ret Xn` with `Xn = retAddr st sz` jumps to `st`'s `pc + sz`;
  `bl_ret` is the pair: a `ret x30` reached with `X30` as `bl` left it
  returns behind the `bl`. `blr_to`: `blr Xn` jumps to `Int64.ofBitVec Xn`.
- `#guard_msgs` runs of the adapter on `bl f; b done; f: ret; done:` and on
  the `adr`/`blr` form: the pcs visited.

The computed target is an ordinary `Int64`: a proof continues at it by
rewriting it to a cell's address (`ret_to`), after which `CellAt` at that
address applies. What the VCGen and runner proof machinery provide for calls is
described in `Lower/README.md`.
-/
import Kraken.Promising.Lower.EventsA64

namespace Kraken.Promising.Lower.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- `X30` after a write of `v` to it. -/
theorem x30_setRegOrZr (regs : Reg64s) (v : BitVec 64) :
    (regs.setRegOrZr (.low (.reg .X30) .W64) v).X30.toBitVec = v := by
  simp [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]

/-- **After `bl`/`blr`, `X30` holds the return address.** -/
theorem x30_after_bl (st : State) (sz : Nat) :
    (st.st.1.regs.setRegOrZr (.low (.reg .X30) .W64) (retAddr st sz)).X30.toBitVec = retAddr st sz :=
  x30_setRegOrZr _ _

/-- A register read as a jump target is the `Int64` of its bits. -/
theorem jump_target_eq (x : BitVec 64) : Int64.ofInt x.signed = Int64.ofBitVec x := by
  apply Int64.toBitVec_inj.mp
  simp [BitVec.signed]

/-- The return address read back as a jump target is the address behind the
call. -/
theorem retAddr_target (st : State) (sz : Nat) :
    Int64.ofInt (retAddr st sz).signed = st.st.2 + .ofNat sz := by
  rw [jump_target_eq, retAddr,
    show (st.st.2 + .ofNat sz).toInt = (st.st.2 + .ofNat sz).toBitVec.toInt from rfl,
    BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]

/-- `Xn` read through `getRegOrZr`. -/
theorem getRegOrZr_reg (regs : Reg64s) (n : XReg) :
    regs.getRegOrZr (.low (.reg n) .W64) = (regs.getXReg n).toBitVec := by
  simp [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]

/-- **`ret Xn` returns to the address behind a call** at `st₀` (`pc₀ + sz₀`)
when `Xn` holds that call's return address. -/
theorem ret_to {st st₀ : State} {sz sz₀ : Nat} {n : XReg}
    (hc : CellAt st (.instr ⟨.W64, .RET (.low (.reg n) .W64)⟩) sz)
    (hx : (st.st.1.regs.getXReg n).toBitVec = retAddr st₀ sz₀) :
    isaLSE2.exec st = some (.done (jumpTo st st.st.1 (st₀.st.2 + .ofNat sz₀))) := by
  rw [exec_ret hc, getRegOrZr_reg, hx, retAddr_target]

/-- **A `bl` … `ret` pair.** `bl target` at `st₀` is a no-event step to the
target with `X30 := retAddr st₀ sz₀`; a `ret` (`ret x30`) reached at `st`
with `X30` as the `bl` left it (the callee preserved `X30`) is a no-event
step back to `pc₀ + sz₀`. -/
theorem bl_ret {st₀ st : State} {sz₀ sz : Nat} {target : ConstExpr}
    (hbl : CellAt st₀ (.instr ⟨.W64, .BL target⟩) sz₀)
    (hret : CellAt st (.instr ⟨.W64, .RET (.low (.reg .X30) .W64)⟩) sz)
    (hx : st.st.1.regs.X30 = (st₀.st.1.regs.setRegOrZr (.low (.reg .X30) .W64) (retAddr st₀ sz₀)).X30) :
    isaLSE2.exec st₀ = some (.done (jumpTo st₀
      { st₀.st.1 with regs := st₀.st.1.regs.setRegOrZr (.low (.reg .X30) .W64) (retAddr st₀ sz₀) }
      (branchTarget st₀ sz₀ target))) ∧
    isaLSE2.exec st = some (.done (jumpTo st st.st.1 (st₀.st.2 + .ofNat sz₀))) :=
  ⟨exec_bl hbl, ret_to hret (by simp only [Reg64s.getXReg]; rw [hx, x30_after_bl])⟩

/-- **`blr Xn`** jumps to the address `Xn` holds (its bits), with `X30 :=`
the return address. -/
theorem blr_to {st : State} {sz : Nat} {n : XReg}
    (hc : CellAt st (.instr ⟨.W64, .BLR (.low (.reg n) .W64)⟩) sz) :
    isaLSE2.exec st = some (.done (jumpTo st
      { st.st.1 with regs := st.st.1.regs.setRegOrZr (.low (.reg .X30) .W64) (retAddr st sz) }
      (Int64.ofBitVec (st.st.1.regs.getXReg n).toBitVec))) := by
  rw [exec_blr hc, getRegOrZr_reg, jump_target_eq]

/-! ### Runs of the adapter

Follow `isaLSE2`'s no-event steps from a thread state built by `mkState`
(laid out at `0x100000`, 4 bytes per instruction) and list the pcs visited,
offset from the base; `halt` at the end address. -/

/-- The pcs of the first `n` no-event steps. -/
def pcs : Nat → State → List String
  | 0, _ => []
  | n + 1, s =>
    match isaLSE2.exec s with
    | none => ["halt"]
    | some (.done s') => s!"{(s.st.2 - 0x100000).toInt}" :: pcs n s'
    | some _ => [s!"{(s.st.2 - 0x100000).toInt}: event"]

/-- `bl f; b done; f: ret; done:` -/
private def blRet : Program :=
  [.instr ⟨.W64, .BL (.label "f")⟩, .instr ⟨.W64, .B (.label "done")⟩, .label "f",
   .instr ⟨.W64, .RET (.low (.reg .X30) .W64)⟩, .label "done"]

/-- `adr x1, f; blr x1; b done; f: ret; done:` -/
private def blrRet : Program :=
  [.instr ⟨.W64, .ADR (.low (.reg .X1) .W64) (.label "f")⟩, .instr ⟨.W64, .BLR (.low (.reg .X1) .W64)⟩,
   .instr ⟨.W64, .B (.label "done")⟩, .label "f", .instr ⟨.W64, .RET (.low (.reg .X30) .W64)⟩, .label "done"]

/-- info: ["0", "8", "4", "halt"] -/
#guard_msgs in
#eval pcs 10 (mkState 0 blRet {})

/-- info: ["0", "4", "12", "8", "halt"] -/
#guard_msgs in
#eval pcs 10 (mkState 0 blrRet {})

end Kraken.Promising.Lower.A64
