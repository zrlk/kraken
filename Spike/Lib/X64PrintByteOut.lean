/-
**A call of `print` with the labels' byte step** (x64):
`print_call_segW` (`Spike/Lib/X64PrintCall.lean`) under a memory side whose
byte step is `print`'s (`ms.bo = ByteOut p lbl`,
`Spike/Lib/ByteOut.lean`). The output row is `emitW_of_out`, the byte
step's closure under local runs is `ByteOut.closed`, and the row's byte
steps (`hlb`) are `ByteOut.load` at each byte. The call site gives, for the
buffer `%rdi`:

- `hpw`: the slice's buffer word is the start of a location placed at `%rdi`;
- `hov`: the bytes `%rdi + i`, `i < printN n m`, do not wrap. This is
  meant to come from placement facts (a placed label inside `Λ.heap`,
  `MemRel.lbl_range`; for an allocated buffer, the allocator's `Call.OK`
  `room` and `cells`: `Spike/Test/X64PrintByteOutHello1.lean`), not from a
  frame condition.

There is no premise on the thread's private memory: that the kernel reads
the bytes from shared memory is the consumer's `hpriv` of
`ByteOut.byteOut_emit`, from a whole-run invariant. A premise "no buffer
byte is in private memory under `F`" here would make the lemma vacuous for
any buffer of 8 bytes or more: no `FStable` frame can state it
(`Spike/Lib/PrivByteVacuous.lean`).
-/
import Spike.Lib.X64PrintCall
import Spike.Lib.ByteOut
import Spike.Lib.PrivByteVacuous

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.ByteOut
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.PrintSrc (PrintC loadC nextC printN printLD)
open PrintCall

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **The byte step of a buffer byte at `print`'s element load**: byte
`k + j` of the slice whose buffer word is the start of the location placed
at `x0` (`hpw`), the bytes not wrapping (`hov`), is `ByteOut` at the
address the output row asks. -/
theorem byteOut_at {pw wn : TermRun.Word} {x0 : BitVec 64} {l nb m k j : Nat} {s : State}
    (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hl : lbl l = some x0.toNat) (hov : x0.toNat + nb < 2 ^ 64)
    (hk : k + j < nb) :
    ByteOut (I := isa) p lbl s ((x0 + BitVec.ofNat 64 k).toNat + j) (loadC pw wn m (k + j))
      (fun c => ∃ mw b, c = nextC pw wn m (k + j) mw b) := by
  have ha : (x0 + BitVec.ofNat 64 k).toNat + j = x0.toNat + (k + j) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [ha]
  exact ByteOut.load hpw hl

/-- **No frame condition says eight bytes are private-free** (x64): an
`FStable` frame under which the bytes `x … x + 7` are absent from the
thread's memory holds of no machine. A lone byte at `x + 3` is invisible to
`DFrame`'s 8-byte loads (`PrivByteVacuous.loadInt_insert_hole`). This is the
guard against putting `print`'s private-memory fact into `F`. -/
theorem hbuf_vacuous {R : Region} {F : MachineData → Prop} (hF : FStable R F) {x : BitVec 64}
    (hbuf : ∀ m, F m → ∀ i < 8, m.dmem[x + BitVec.ofNat 64 i]? = none) : ∀ m, ¬ F m := by
  intro m hm
  have hm' := hF m { m with dmem := m.dmem.insert (x + 3#64) 0 } hm
    (fun a _ _ => PrivByteVacuous.loadInt_insert_hole (hbuf m hm) 0 a)
  have := hbuf _ hm' 3 (by omega)
  simp only [PrivByteVacuous.getElem?_insert_self] at this
  exact absurd this (by simp)

/-- **`print_call_segW` with the labels' byte step** (`ms.bo = ByteOut abi
p lbl`): the output row, its closure and the byte steps are discharged;
the call site gives the buffer facts `hpw`, `hov` (see the module
docstring for where `hov` comes from, and why there is no private-memory
premise: `hbuf_vacuous`). -/
theorem print_call_segWB {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    {nC : ND}
    {pw wn : AS → TermRun.Word} {n m : AS → Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ nC.o.sp - 8 + -40) (hhi : nC.o.sp - 8 + 16 ≤ R.hi) (hk8 : (nC.o.sp - 8) % 8 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (n σ) (m σ) 0 c)
    (hN : ∀ σ c, nC.J σ c → (σ.regs.get64 .rsi).toNat = printN (n σ) (m σ))
    (hm : ∀ σ c, nC.J σ c → 8 * m σ < 2 ^ 63)
    (hpw : ∀ σ c, nC.J σ c → ∃ l, (pw σ).val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σ.regs.get64 .rdi).toNat)
    (hov : ∀ σ c, nC.J σ c → (σ.regs.get64 .rdi).toNat + printN (n σ) (m σ) < 2 ^ 64)
    (hW : ∀ σC c, nC.J σC c → PrintA.PrintAW σC.regs.rbp.toBitVec (σC.slot nC.o.sp) (σC.regs.get64 .rdi)
      (σC.regs.get64 .rsi).toNat (pcS pw wn n m σC) (pcS pw wn n m σC) W K exe endPc (pR (nC.o.sp - 8) R)
      (pF (nC.o.sp - 8) R F))
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the output row, assumed
    -- the memory side
    (hK : ms.K = some Scc.Sem.X64.abi) (hbo : ms.bo = ByteOut (I := isa) p lbl)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF (nC.o.sp - 8) R F m) → ∀ s c',
      At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF (nC.o.sp - 8) R F m) → ∀ s c',
      At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (n σC) (m σC) k c1 → ms.we s c1)
    -- where the return and the abort land
    (hret : ∀ σC c σR c', nC.J σC c → σR.regs.get64 .rbp = σC.regs.rbp.toBitVec →
      PrintC (pw σC) (wn σC) (n σC) (m σC) (printN (n σC) (m σC)) c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec (σC.slot nC.o.sp), ⟨nC.o.sp + 8, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.get64 .rdi = 4 → PrintC (pw σC) (wn σC) (n σC) (m σC) k c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp - 8 + -40, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  have hE : PrintA.EmitW W K p lbl ms (ByteOut (I := isa) p lbl) ms.we := hbo ▸ PrintA.emitW_of_out
  refine print_call_segW hp hend hprog hF hR hlo hhi hk8 hpc hP0 hN hm hW hd hE hK
    (fun _ _ _ _ _ _ hr h hΦ => ByteOut.closed hr h hΦ) hWs ?_ hwe hret habort
  intro σC c hJ _ _ _ _ _ k j hk
  obtain ⟨l, hpw', hl⟩ := hpw σC c hJ
  exact byteOut_at hpw' hl (hov σC c hJ) hk

end Fn

end Spike.Lib.X64
