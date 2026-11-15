import Spike.Test.Ret0LinkedA64GC

/-!
# `ret0.w` on AArch64 after the granule pass, end to end at the linked executable's layout

`Scc/Test/elf/ret0a64g/ret0` is `scc --granule`'s text for `ret0.w`
(`ret0.s` next to it), linked as `Ret0LinkedA64`'s. The text is the
certificate's `asm` with the pass's tail before `scc_text_end` (a `.zero`
filler, `.Lgw0:` and the descriptor word) and the `.text.scc_galign` section
after it (`asmG`, checked below). Its parse is the certificate's cells with
the end label replaced by the tail `tailG` (checked below), and the same
data sections: the output `outF := withTail outLit tailG`.

At the executable's layout `ΛG`, each component of `placeOKAt` of `outF`
holds by `decide +kernel` (`ret0G_placeOKAt`), so `ret0_linked_correctG`
is `a64_scc_correctE_text_closedAt_tail` at `ΛG`: `Ret0LinkedA64`'s statement
at the post-pass text and layout, its only premise the parse check `hpa`.
The lowering's success is `Ret0LinkedA64.ret0_placeOKAt`'s (the pre-pass
output at the pre-pass layout); no post-pass certificate is used.
-/

namespace Spike.Test.Ret0LinkedA64G

open Scc.Cert.PlaceOK
open SccCertificate (asm out outLit out_eq placeCfg)
open Spike.Lib.LowerA64 (withTail)

/-- **`placeOKAt` of the output with the tail at `ΛG`**, from its components. -/
theorem ret0G_placeOKAt : A64.placeOKAt placeCfg ΛG (withTail out tailG) = true := by
  rw [out_eq]
  exact A64.placeOKAt_of ret0G_a1 ret0G_a2 ret0G_a3 ret0G_a4 ret0G_a5 ret0G_a6 ret0G_a7 ret0G_a8 ret0G_a9
    ret0G_a11 ret0G_a12

set_option maxRecDepth 100000 in
/-- **`ret0.w` compiled for AArch64 with the granule pass is correct at the
linked executable's layout**, at every admissible entry state, for every
budget `B` and memory model `arch`: `Ret0LinkedA64.ret0_linked_correct`'s
statement at the post-pass text `asmG` and layout `ΛG`, given the parse
check `hpa` (`a64_scc_correctE_text_closedAt_tail`; the lowering's success
from `Ret0LinkedA64.ret0_placeOKAt`). -/
theorem ret0_linked_correctG (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.A64.parsesTo asmG (withTail out tailG).prog (withTail out tailG).secs = true) :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src)
      { ΛG with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseA64.main } B
      asmG :=
  Spike.Lib.LowerA64.a64_scc_correctE_text_closedAt_tail (cfg := SccCertificate.config) ΛG
    SccCertificate.prog_accepted
    (Spike.Lib.LowerA64.lowerAll?_ok_of_placeOK Spike.Test.Ret0LinkedA64.ret0_placeOKAt)
    ret0G_placeOKAt hpa

-- `hpa`, by compiled evaluation: exactly `ret0_linked_correctG`'s hypothesis.
set_option maxRecDepth 100000 in
#guard Scc.Cert.Link.A64.parsesTo asmG outF.prog outF.secs

/-- At any layout passing the placement check for some output, the 64 KiB
stack at `2 ^ 32` is admissible at the theorem's layout (stated over a
variable layout, so that instantiating it at `ΛG` reduces nothing). -/
theorem witness_of {Λ : Scc.Sem.Layout} {o : A64.Out} (h : A64.placeOKAt placeCfg Λ o = true) :
    Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseA64.main } :=
  Scc.Sem.Entry.ok_witness (Scc.Cert.PlaceOK.A64.below32_of_placeOKAt h)

/-- **The entry quantifier is not vacuous at `ΛG`**. -/
theorem ret0_linked_witnessG :
    Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩
      { ΛG with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseA64.main } :=
  witness_of ret0G_placeOKAt

end Spike.Test.Ret0LinkedA64G

/--
info: 'Spike.Test.Ret0LinkedA64G.ret0_linked_correctG' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Test.Ret0LinkedA64G.ret0_linked_correctG

/--
info: 'Spike.Test.Ret0LinkedA64G.ret0_linked_witnessG' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Test.Ret0LinkedA64G.ret0_linked_witnessG
