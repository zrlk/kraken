/-
**hello.w's `wc_rodata` from the allocator's return inside the start's level: the load step** (x86-64; the
own-free part of the twin of `Spike/Lib/A64HelloRdPostWfSF.lean`): a load of a word unmapped under the frame
condition steps and writes nothing at `HelloWf.WSHFg`'s write obligation `NoWrC … fs`. The level's statements
(AArch64 `blkW_rpWSHF`, `nodeW_rpWSHF`, `rdPostW_WSHF`, `mB1W_WSHF`) are at `ownGHXW` only,
`X64HelloRdPostWfSFX`'s `blkW_rpWSHFg`, `nodeW_rpWSHFg`, `rdPostW_WSHX`, `mB1W_WSHX`, which reuse this step.

- `ld_stepHF`: a load of a word unmapped under `F` steps to `pc + z` and writes nothing (at `NoWrC … fs`).

## Differences from the AArch64 version

- The load is `movq k(%rcx), %rax` at the buffer `%rax` of `.x15`'s entry (`bAddr_rcx_rax`; AArch64's
  `ldr x9, [x10, #i]` at `x0`); `ld_stepHF` goes through `WakeWf.ld_step`.
-/
import Spike.Lib.X64HelloRdPostWI
import Spike.Lib.X64HelloRdPreWI
import Spike.Lib.X64HelloAllocWSF
import Spike.Lib.X64HelloWcWf
import Spike.Lib.X64SetupPlaced
import Spike.Lib.X64WakeWfW2

namespace Spike.Lib.X64.HelloPh.RdWfSF

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (ND NodeW At ldDir bAddr mB eaddr_mB agrees_of_decls)
open Spike.Lib.X64.WakeWf (NoWrC)
open Spike.Lib.X64.HelloPh.WcW (freeNH)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt eaddr exec_load_agrees)

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {K : State → State → Prop} {fs : List TermRun.Frame}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s) (hfs : fs = [] ∨ fs = [frM])

include hp hlo hΛ hlab hsite hcl hX0 hfs

/-! ## A load inside `WSHFg` -/

omit hΛ hlab hcl hX0 hfs in
/-- **A load `movq i(%b), %r` of a word unmapped under `F`** (`ha`) steps to `pc + z` and writes nothing. -/
theorem ld_stepHF {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(ldDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none) :
    (∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s' : State, TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z) ∧
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) L.exe L.endPc R F n := by
  have hI := instOkH hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hb' : blockAtB L.prog l k [(ldDir b i r, z)] = true := by rw [hp]; exact hb
  refine ⟨Spike.Lib.X64.WakeWf.ld_step hI hb' he ha, Spike.Lib.X64.WakeWf.nodeW_noWrC fun s c hA => ?_⟩
  obtain ⟨hs, hn, hdc, hpc, σ, hA', hD, hJc⟩ := hA
  have hc := Spike.Lib.X64.Rt.cellOf hI hb' he hs hn hpc
  have ha' : eaddr s z (mB b i) = bAddr σ.regs b i := (eaddr_mB s z b i).trans (by rw [hA'.regs]; rfl)
  exact ⟨Spike.Lib.X64ConsumerA.noWr_load (exec_load_agrees hc ha' (ha σ c s.st.1 hJc hD) (agrees_of_decls hdc _ _)),
    fun _ h => h⟩

end Gen

end Spike.Lib.X64.HelloPh.RdWfSF

/-! ## Axioms -/
