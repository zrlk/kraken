/-
**`print_call_segWB` at `hello1.w`'s print call** (AArch64; a non-vacuity
regression of `Spike/Lib/A64PrintByteOut.lean`): `wc_main`'s call of
`scc_rt_print` (`aN … .call`, `Spike/Lib/A64Hello1BodyA.lean`, the call of
`main`'s `print{q}(sl)` after `split` and `unpack`), against the source's
`print` loop on the slice `rodata` returns.

The body's entry invariant `bJ` holds what the setup block delivers:
`rdPostS` (`Spike/Lib/A64Hello1RodataSetupG.lean`), the slice's base at a
label `l` placed at `A` in the arena's cells, the offset word `0`, the
length `2` and the count `13`, in `wc_main`'s slots (`-96`, `-88`, `-80`,
`-72`). From these alone `print_call_segWB`'s call-site premises are
discharged:

- `hP0`, `hN`, `hm`: the source at `print`'s loop top, the count
  `min(13, 2·8) = printN 13 2` (`wcC_x1`), `8·2 < 2^63`;
- `hpw`: the buffer word is `rodata`'s `cst (.loc ⟨l, 0⟩ 0)` (`envR`) and
  `x0` is the base (`wcC_x0`, offset word `0`), placed at `l`;
- `hov`: `A + 13 < 2^64`, from the allocator's facts (`A = heap + 16·old
  + off 2 τ8`, `old + units 2 τ8 ≤ cells`), the setup's premises on the
  call (`hQ : rdQ.OK`: its `off`, and the arena's `room` and `cells`,
  `heap + 2^46 ≤ 2^64` with `2^22` cells; `hu : units 2 τ8 = 3`). No new
  premise is needed: the arena bound a consumer would take from the
  placement (`heap_hov_of_placeOKAt`, `Spike/Lib/ArenaBound.lean`) is here
  already part of the allocator's call premises.

No private-memory premise is asked (see `print_call_segWB`'s docstring).
The rest (`print`'s states inside `W`, its system call, where the return
and the abort land) are `print_call_segWB`'s as they are, as in
`hello1_wc_bodyA_segW`.

**Caveat: one label at a time.** `print_call_segWB` takes the buffer word
as a function of the call state (`pw : AS → Word`), and the source word
depends on the allocation's label `l`, which no register determines. The
regression fixes `l` (`bJ … l`, `bP l`); a whole-program proof takes the
union over `l` of these segments (the pre `∃ l, At … (bJ … l)`).
-/
import Spike.Lib.A64PrintByteOut
import Spike.Lib.A64Hello1BodyA
import Spike.Lib.A64Hello1RodataSetupG

namespace Spike.Test.A64PrintByteOutHello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Hello1
open Spike.Lib.ByteOut (ByteOut)
open Spike.Lib.PrintSrc (PrintC printN printLD)
open Spike.Lib.A64.Flow.PrintCall (pcS)
open Spike.Lib.Hello1RodataSrc (τ8)
open Scc.Cert.Rt.A64 (Lays endOf)

/-- `rodata`'s buffer word at label `l` (`envR`). -/
def pwL (l : WeakMem.AllocLabel) : TermRun.Word := TermRun.cst (.loc ⟨l, 0⟩ 0)

/-- `rodata`'s count word, `13`. -/
def wn13 : TermRun.Word := TermRun.cst (.num 13)

/-- **`wc_main`'s body entry, as the setup delivers it** for label `l`:
the base at `-96` placed at `A` in the arena's cells (`rdPostS`), the
offset word `0` at `-88`, the length `2` at `-80`, the count `13` at
`-72`. -/
def bJ (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide isaLSE2) (l : WeakMem.AllocLabel) (σ : AS)
    (_c : Ctl) : Prop :=
  ∃ A old : Nat, lbl l = some A ∧ (σ.slot (-96)).toNat = A ∧ σ.slot (-88) = 0#64 ∧ σ.slot (-80) = 2#64 ∧
    σ.slot (-72) = 13#64 ∧ A = ms.heap + 16 * old + ms.off 2 τ8 ∧ old + ms.units 2 τ8 ≤ ms.cells

/-- The source inside `print` with `k` bytes out, on `rodata`'s slice. -/
def bP (l : WeakMem.AllocLabel) (_σ : AS) (k : Nat) (c : Ctl) : Prop := PrintC (pwL l) wn13 13 2 k c

/-- The buffer `x0` at the call is the base. -/
theorem bJ_x0 {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {l : WeakMem.AllocLabel} {σ0 : AS}
    {c0 : Ctl} (lab : Label → Int64) (h : bJ lbl ms l σ0 c0) :
    (wcC lab σ0).regs.X0.toBitVec.toNat = (σ0.slot (-96)).toNat := by
  obtain ⟨-, -, -, -, h88, -⟩ := h
  rw [wcC_x0, h88]
  simp [BitVec.take]

/-- The count at the call is `printN 13 2`. -/
theorem bJ_x1 {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {l : WeakMem.AllocLabel} {σ0 : AS}
    {c0 : Ctl} (lab : Label → Int64) (h : bJ lbl ms l σ0 c0) :
    (wcC lab σ0).regs.X1.toBitVec.toNat = printN 13 2 := by
  obtain ⟨-, -, -, -, -, h80, h72, -⟩ := h
  rw [wcC_x1, h80, h72]
  decide

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **`hello1.w`'s print call through `print_call_segWB`**, for the label
`l` (see the module docstring): the call-site premises `hP0`, `hN`, `hm`,
`hpw`, `hov` discharged from `bJ` (the setup's post), `hQ` and `hu`. -/
theorem hello1_print_segWB (l : WeakMem.AllocLabel) {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (hd : p.find? (·.name == "printL") = some printLD)
    (hK : ms.K = some Scc.Sem.A64.abi) (hbo : ms.bo = ByteOut (I := isaLSE2) p lbl)
    -- the allocator's premises the setup takes
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    -- `print_call_segWB`'s premises on `W` and the landings, as they are
    (hW : ∀ σC c, (aN (_root_.Executable.labels exe).label (bJ lbl ms l) (bP l) .call).J σC c →
      Spike.Lib.A64.PrintA.PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
        σC.regs.X1.toBitVec.toNat
        (pcS (fun _ => pwL l) (fun _ => wn13) (fun _ => 13) (fun _ => 2) σC)
        (pcS (fun _ => pwL l) (fun _ => wn13) (fun _ => 13) (fun _ => 2) σC) W K exe endPc
        (PrintCall.pR (-96) R) (PrintCall.pF (-96) R F))
    (hWs : ∀ σC c, (aN (_root_.Executable.labels exe).label (bJ lbl ms l) (bP l) .call).J σC c →
      ∀ (F' : MachineData → Prop) s c', At exe endPc (PrintCall.pR (-96) R) F'
      (PrintCall.pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pwL l) (fun _ => wn13) (fun _ => 13) (fun _ => 2))
        (pcS (fun _ => pwL l) (fun _ => wn13) (fun _ => 13) (fun _ => 2)) σC .svc) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hwe : ∀ σC c, (aN (_root_.Executable.labels exe).label (bJ lbl ms l) (bP l) .call).J σC c →
      ∀ (F' : MachineData → Prop) s c', At exe endPc (PrintCall.pR (-96) R) F'
      (PrintCall.pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pwL l) (fun _ => wn13) (fun _ => 13) (fun _ => 2))
        (pcS (fun _ => pwL l) (fun _ => wn13) (fun _ => 13) (fun _ => 2)) σC .svc) s c' →
      ∀ k c1, PrintC (pwL l) wn13 13 2 k c1 → ms.we s c1)
    (hret : ∀ σC c σR c', (aN (_root_.Executable.labels exe).label (bJ lbl ms l) (bP l) .call).J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      PrintC (pwL l) wn13 13 2 (printN 13 2) c' →
      (∀ k, R.Off k → ¬ (PrintCall.pR (-96) R).Off (k - -96) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨-96, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, (aN (_root_.Executable.labels exe).label (bJ lbl ms l) (bP l) .call).J σC c →
      σR.regs.X0 = 4 → PrintC (pwL l) wn13 13 2 k c' →
      (∀ k, R.Off k → ¬ (PrintCall.pR (-96) R).Off (k - -96) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨-96 + -48, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F (aN (_root_.Executable.labels exe).label (bJ lbl ms l) (bP l) .call))
      (Next exe endPc R F N E) := by
  have hoff : ms.off 2 τ8 = 8 := by
    have h := hQ.off
    simp only [rdQ] at h
    rw [h]
    decide
  refine print_call_segWB (nC := aN (_root_.Executable.labels exe).label (bJ lbl ms l) (bP l) .call)
    (pw := fun _ => pwL l) (wn := fun _ => wn13) (n := fun _ => 13) (m := fun _ => 2)
    hp hend SccCode.hello1_print hF hR hal (by show R.lo ≤ -96 + -48; omega) (by show (-96 : Int) < R.hi; omega)
    (by show (-96 : Int) % 16 = 0; decide) rfl ?_ ?_ ?_ ?_ ?_ hW hd hK hbo
    (fun σC c hJ F' _ => hWs σC c hJ F') (fun σC c hJ F' _ => hwe σC c hJ F') hret habort
  · rintro σ c ⟨σ0, c0, -, -, hP⟩
    exact hP
  · rintro σ c ⟨σ0, c0, hJ, rfl, -⟩
    exact bJ_x1 _ hJ
  · intro _ _ _
    decide
  · rintro σ c ⟨σ0, c0, hJ, rfl, -⟩
    obtain ⟨A, old, hl, h96, -⟩ := id hJ
    refine ⟨l, rfl, ?_⟩
    rw [bJ_x0 _ hJ, h96]
    exact hl
  · rintro σ c ⟨σ0, c0, hJ, rfl, -⟩
    obtain ⟨A, old, -, h96, -, -, -, hA, hold⟩ := id hJ
    rw [bJ_x0 _ hJ, h96, hA, hoff]
    rw [hu] at hold
    have hroom := hQ.room
    have hcells := hQ.cells
    show ms.heap + 16 * old + 8 + 13 < 2 ^ 64
    omega

end Spike.Test.A64PrintByteOutHello1
