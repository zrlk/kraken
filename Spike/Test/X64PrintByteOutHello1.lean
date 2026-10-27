/-
**`print_call_segWB` at `hello1.w`'s print call** (x86-64; a non-vacuity
regression of `Spike/Lib/X64PrintByteOut.lean`): `wc_main`'s call of
`scc_rt_print` (`aN … .call`, `Spike/Lib/X64Hello1BodyA.lean`, the call of
`main`'s `print{q}(sl)` after `split` and `unpack`), against the source's
`print` loop on the slice `rodata` returns.

The body's entry invariant `bJ` holds what the setup block delivers:
`rdPostS` (`Spike/Lib/X64Hello1RodataSetupG.lean`), the slice's base at a
label `l` placed at `A` in the arena's cells, the offset word `0`, the
length `2` and the count `13`, in `wc_main`'s slots (`-16`, `-24`, `-32`,
`-40`). From these alone `print_call_segWB`'s call-site premises are
discharged:

- `hP0`, `hN`, `hm`: the source at `print`'s loop top, the count
  `min(13, 2·8) = printN 13 2` (`wcC_rsi`), `8·2 < 2^63`;
- `hpw`: the buffer word is `rodata`'s `cst (.loc ⟨l, 0⟩ 0)` (`envR`) and
  `%rdi` is the base (`wcC_rdi`, offset word `0`), placed at `l`;
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
import Spike.Lib.X64PrintByteOut
import Spike.Lib.X64Hello1BodyA
import Spike.Lib.X64Hello1RodataSetupG

namespace Spike.Test.X64PrintByteOutHello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Hello1
open Spike.Lib.ByteOut (ByteOut)
open Spike.Lib.PrintSrc (PrintC printN printLD)
open Spike.Lib.X64.PrintCall (pcS)
open Spike.Lib.Hello1RodataSrc (τ8)
open Scc.Cert.Rt.X64 (Lays endOf)

/-- `rodata`'s buffer word at label `l` (`envR`). -/
def pwL (l : WeakMem.AllocLabel) : TermRun.Word := TermRun.cst (.loc ⟨l, 0⟩ 0)

/-- `rodata`'s count word, `13`. -/
def wn13 : TermRun.Word := TermRun.cst (.num 13)

/-- **`wc_main`'s body entry, as the setup delivers it** for label `l`:
the base at `-16` placed at `A` in the arena's cells (`rdPostS`), the
offset word `0` at `-24`, the length `2` at `-32`, the count `13` at
`-40`. -/
def bJ (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide isa) (l : WeakMem.AllocLabel) (σ : AS)
    (_c : Ctl) : Prop :=
  ∃ A old : Nat, lbl l = some A ∧ (σ.slot (-16)).toNat = A ∧ σ.slot (-24) = 0#64 ∧ σ.slot (-32) = 2#64 ∧
    σ.slot (-40) = 13#64 ∧ A = ms.heap + 16 * old + ms.off 2 τ8 ∧ old + ms.units 2 τ8 ≤ ms.cells

/-- The source inside `print` with `k` bytes out, on `rodata`'s slice. -/
def bP (l : WeakMem.AllocLabel) (_σ : AS) (k : Nat) (c : Ctl) : Prop := PrintC (pwL l) wn13 13 2 k c

/-- The buffer `%rdi` at the call is the base. -/
theorem bJ_rdi {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {l : WeakMem.AllocLabel} {σ0 : AS}
    {c0 : Ctl} (lab : Label → Int64) (fl : StatusFlags) (h : bJ lbl ms l σ0 c0) :
    ((wcC lab σ0 fl).regs.get64 .rdi).toNat = (σ0.slot (-16)).toNat := by
  obtain ⟨-, -, -, -, h24, -⟩ := h
  rw [wcC_rdi, h24]
  simp [BitVec.take]

/-- The count at the call is `printN 13 2`. -/
theorem bJ_rsi {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {l : WeakMem.AllocLabel} {σ0 : AS}
    {c0 : Ctl} (lab : Label → Int64) (fl : StatusFlags) (h : bJ lbl ms l σ0 c0) :
    ((wcC lab σ0 fl).regs.get64 .rsi).toNat = printN 13 2 := by
  obtain ⟨-, -, -, -, -, h32, h40, -⟩ := h
  rw [wcC_rsi, h32, h40]
  decide

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **`hello1.w`'s print call through `print_call_segWB`**, for the label
`l` (see the module docstring): the call-site premises `hP0`, `hN`, `hm`,
`hpw`, `hov` discharged from `bJ` (the setup's post), `hQ` and `hu`. -/
theorem hello1_print_segWB (l : WeakMem.AllocLabel) {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 8 ≤ R.hi)
    (hd : p.find? (·.name == "printL") = some printLD)
    (hK : ms.K = some Scc.Sem.X64.abi) (hbo : ms.bo = ByteOut (I := isa) p lbl)
    -- the allocator's premises the setup takes
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    -- `print_call_segWB`'s premises on `W` and the landings, as they are
    (hW : ∀ σC c, (aN (_root_.Executable.labels exe).label R (bJ lbl ms l) (bP l) .call).J σC c →
      PrintA.PrintAW σC.regs.rbp.toBitVec (σC.slot (-96)) (σC.regs.get64 .rdi) (σC.regs.get64 .rsi).toNat
        (pcS (fun _ => pwL l) (fun _ => wn13) (fun _ => 13) (fun _ => 2) σC)
        (pcS (fun _ => pwL l) (fun _ => wn13) (fun _ => 13) (fun _ => 2) σC) W K exe endPc
        (PrintCall.pR (-96 - 8) R) (PrintCall.pF (-96 - 8) R F))
    (hWs : ∀ σC c, (aN (_root_.Executable.labels exe).label R (bJ lbl ms l) (bP l) .call).J σC c →
      ∀ (F' : MachineData → Prop) s c', At exe endPc (PrintCall.pR (-96 - 8) R) F'
      (PrintCall.pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pwL l) (fun _ => wn13) (fun _ => 13) (fun _ => 2))
        (pcS (fun _ => pwL l) (fun _ => wn13) (fun _ => 13) (fun _ => 2)) (-96) σC .sys) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hwe : ∀ σC c, (aN (_root_.Executable.labels exe).label R (bJ lbl ms l) (bP l) .call).J σC c →
      ∀ (F' : MachineData → Prop) s c', At exe endPc (PrintCall.pR (-96 - 8) R) F'
      (PrintCall.pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pwL l) (fun _ => wn13) (fun _ => 13) (fun _ => 2))
        (pcS (fun _ => pwL l) (fun _ => wn13) (fun _ => 13) (fun _ => 2)) (-96) σC .sys) s c' →
      ∀ k c1, PrintC (pwL l) wn13 13 2 k c1 → ms.we s c1)
    (hret : ∀ σC c σR c', (aN (_root_.Executable.labels exe).label R (bJ lbl ms l) (bP l) .call).J σC c →
      σR.regs.get64 .rbp = σC.regs.rbp.toBitVec → PrintC (pwL l) wn13 13 2 (printN 13 2) c' →
      (∀ k, R.Off k → ¬ (PrintCall.pR (-96 - 8) R).Off (k - (-96 - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec (σC.slot (-96)), ⟨-96 + 8, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, (aN (_root_.Executable.labels exe).label R (bJ lbl ms l) (bP l) .call).J σC c →
      σR.regs.get64 .rdi = 4 → PrintC (pwL l) wn13 13 2 k c' →
      (∀ k, R.Off k → ¬ (PrintCall.pR (-96 - 8) R).Off (k - (-96 - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨-96 - 8 + -40, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F (aN (_root_.Executable.labels exe).label R (bJ lbl ms l) (bP l) .call))
      (Next exe endPc R F N E) := by
  have hoff : ms.off 2 τ8 = 8 := by
    have h := hQ.off
    simp only [rdQ] at h
    rw [h]
    decide
  refine print_call_segWB (nC := aN (_root_.Executable.labels exe).label R (bJ lbl ms l) (bP l) .call)
    (pw := fun _ => pwL l) (wn := fun _ => wn13) (n := fun _ => 13) (m := fun _ => 2)
    hp hend SccCode.hello1_print hF hR (by show R.lo ≤ -96 - 8 + -40; omega)
    (by show (-96 : Int) - 8 + 16 ≤ R.hi; omega) (by show ((-96 : Int) - 8) % 8 = 0; decide) rfl
    ?_ ?_ ?_ ?_ ?_ hW hd hK hbo
    (fun σC c hJ F' _ => hWs σC c hJ F') (fun σC c hJ F' _ => hwe σC c hJ F') hret habort
  · rintro σ c ⟨σ0, c0, fl, -, -, hP⟩
    exact hP
  · rintro σ c ⟨σ0, c0, fl, ⟨hJ, -⟩, rfl, -⟩
    exact bJ_rsi _ fl hJ
  · intro _ _ _
    decide
  · rintro σ c ⟨σ0, c0, fl, ⟨hJ, -⟩, rfl, -⟩
    obtain ⟨A, old, hl, h16, -⟩ := id hJ
    refine ⟨l, rfl, ?_⟩
    rw [bJ_rdi _ fl hJ, h16]
    exact hl
  · rintro σ c ⟨σ0, c0, fl, ⟨hJ, -⟩, rfl, -⟩
    obtain ⟨A, old, -, h16, -, -, -, hA, hold⟩ := id hJ
    rw [bJ_rdi _ fl hJ, h16, hA, hoff]
    rw [hu] at hold
    have hroom := hQ.room
    have hcells := hQ.cells
    show ms.heap + 16 * old + 8 + 13 < 2 ^ 64
    omega

end Spike.Test.X64PrintByteOutHello1
