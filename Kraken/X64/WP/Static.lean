module

public import Kraken.StateCfg
public import Kraken.X64.WP.Image

/-!
# The static frame

A convention for procedure specifications (triples about a callee's body, used
at a call through `Program.WP.callSpec_of_triple`): every procedure is granted
the loaded image `Host.Image` in its precondition and gives it back in its
postcondition. A contract then never lists the constants its procedure reads,
and a callee cannot read a constant that its caller's contract forgot: all of
`Host.Image` is always granted.

Nothing here is a new rule. Under `CallSpec` the caller takes `Host.Image` back
from the callee's postcondition, as it takes back any other cell, so the
callee's proof must return it, which a procedure that only reads constants does
trivially. `StaticPre`/`StaticPost` spell the convention's share once. An
assumed external routine is granted the image too, which assumes of it only
that it leaves the image alone.
-/

public section

namespace Program.WP

/-- The convention's share of a procedure's precondition: the image is loaded, besides
`R`. -/
@[expose] def StaticPre [Host] (R : DataMem → Prop) (s : MachineData) : Prop :=
  s.dmem =⋆ Host.Image ⋆ R

/-- The convention's share of a procedure's postcondition: the image is still loaded,
besides `R`. -/
@[expose] def StaticPost [Host] (R : DataMem → Prop) (t : MachineData) : Prop :=
  t.dmem =⋆ Host.Image ⋆ R

/-- The image survives the call's push of the return address into a slot the frame
owns. -/
theorem StaticPre.pushRa [Host] {R : DataMem → Prop} {s : MachineData}
    (h : StaticPre (Mem.Blocks [(s.regs.get64 .rsp - 8#64, 8)] ⋆ R) s) (ra : Int64) :
    StaticPre (Mem.Blocks [(s.regs.get64 .rsp - 8#64, 8)] ⋆ R) (s.pushRa ra) := by
  unfold StaticPre at h ⊢
  rw [Std.ExtHashMap.sep_comm_l] at h ⊢
  rw [MachineData.dmem_pushRa]
  exact Mem.Blocks.storeInt h (Mem.Blocks.Inside.base (Nat.le_refl 8)) _

end Program.WP

end
