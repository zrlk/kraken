/-
**Off wake's exit calls and transfer sites, decided by label** (AArch64, main after the spawn): the pc test
`Spike.Lib.A64AbOffL.PcOff` (the `writeErr`/`threads`
abort exits and the take/release sites), stated here unfolded, at a pc
`label l + 4k` of wake.w's listing, decided on the listing (`abChk`,
through `Spike.Lib.A64.PcRuns.pcIn_iff`). The listing is wake.w's
certificate (`Spike/Test/Cert/A64WakeCert.s`).

- `abRuns`: the four labels' first instructions.
- `abChk l k0 len`: none of the instructions `k0 .. k0 + len` after `l` is
  one of them.
- `abOff_at`: at such a pc the pc is none of the four labels.
- `wait_tlsChk`, `wait_tlsCode`: `wc_waitLoop`'s limit load, off them, and
  its code.
- `seg_waitTlsW`: the limit load as a segment inside a state predicate `W`
  with no outside moves (`rtld_ndW`), from any node at its pc to any node
  after it.
- `seg_waitTlsLim`: `seg_waitTlsW` inside `TlsW lab A c0` (`WaitLoop`'s
  `htls`) with the limit word's facts (`LimOk` at `tp + 8`, room up to
  `x9`'s address `R.addr (-32)`, `tp + 8 ≠ A`) for `x10 = tp` and control
  `c0` at the load's node; the landing node's invariant from the load's room.
-/
import Spike.Lib.A64PcRuns
import Spike.Lib.A64WakeLabels
import Spike.Lib.A64CodeSegs
import Spike.Lib.A64AllocNodes
import Spike.Lib.A64Ret0
import Spike.Lib.A64AbOffLDef

namespace Spike.Lib.A64.Flow.Worker.Wake.AbOffAt

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf labelIdx run blockAt)
open Spike.Lib.A64.PcRuns (PcIn runsOk inRuns pcIn_iff)
open Spike.Lib.A64.WakeLabels (wakeProg)

/-- **The exit calls of the `writeErr` and `threads` abort stubs, and the
take and release sites.** -/
def abRuns : List (Label × Nat × Nat) :=
  [("scc_rt_abort_write_exit", 0, 1), ("scc_rt_abort_threads_exit", 0, 1),
    ("scc_rt_take_site", 0, 1), ("scc_rt_release_site", 0, 1)]

theorem wake_abRunsOk : runsOk wakeProg abRuns = true := by decide +kernel

/-- **None of the instructions `k0 .. k0 + len` after `l` is an exit
call**, decided on the listing. -/
def abChk (l : Label) (k0 len : Nat) : Bool :=
  (labelIdx wakeProg l).isSome && decide (k0 + len ≤ (run wakeProg l).length) &&
    (List.range len).all fun j => !inRuns wakeProg abRuns l (k0 + j)

section Inst

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe wakeProg kp)
include hp

/-- **Off the exit calls at a decided pc** (`AbOffL`, unfolded): the
instruction `k0 + k` after `l`, `k < len`, with `abChk l k0 len`. -/
theorem abOff_at {l : Label} {k0 len : Nat} (hchk : abChk l k0 len = true) {s : State} {k : Nat}
    (hk : k < len) (he : s.exe = exe)
    (hs : s.st.2 = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0) + Int64.ofNat (4 * k)) :
    s.st.2 ≠ (_root_.Executable.labels exe).label "scc_rt_abort_write_exit" ∧
      s.st.2 ≠ (_root_.Executable.labels exe).label "scc_rt_abort_threads_exit" ∧
      s.st.2 ≠ (_root_.Executable.labels exe).label "scc_rt_take_site" ∧
      s.st.2 ≠ (_root_.Executable.labels exe).label "scc_rt_release_site" := by
  simp only [abChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at hchk
  obtain ⟨⟨hl, hlen⟩, hall⟩ := hchk
  rw [Int64.add_assoc, ← Int64.ofNat_add, ← Nat.mul_add] at hs
  have hnot : ¬ PcIn abRuns s := by
    rw [pcIn_iff hp wake_abRunsOk he hl (by omega) hs, hall k hk]; exact Bool.false_ne_true
  refine ⟨fun h => hnot ⟨("scc_rt_abort_write_exit", 0, 1), by simp [abRuns], 0, Nat.le_refl 0,
      Nat.zero_lt_one, ?_⟩,
    fun h => hnot ⟨("scc_rt_abort_threads_exit", 0, 1), by simp [abRuns], 0, Nat.le_refl 0,
      Nat.zero_lt_one, ?_⟩,
    fun h => hnot ⟨("scc_rt_take_site", 0, 1), by simp [abRuns], 0, Nat.le_refl 0, Nat.zero_lt_one, ?_⟩,
    fun h => hnot ⟨("scc_rt_release_site", 0, 1), by simp [abRuns], 0, Nat.le_refl 0,
      Nat.zero_lt_one, ?_⟩⟩ <;>
  · rw [he, h]; exact (Spike.Lib.A64.Flow.ofNat4_zero _).symm

end Inst

/-! ## Checks on wake's listing -/

/-- `wc_waitLoop`'s limit load (`ldr x10, [x10, #8]`, the third
instruction after its stack check's label) is off the exit calls. -/
theorem wait_tlsChk : abChk (WakeLabels.pfx ++ ".stack_check") 2 1 = true := by decide +kernel

/-- The limit load's code (`WaitLoop.Code` has no field for it). -/
theorem wait_tlsCode : blockAt wakeProg (WakeLabels.pfx ++ ".stack_check") 2 [ldrDir .X10 .X10 8] = true := by
  decide +kernel

/-! ## `wc_waitLoop`'s limit load -/

section Tls

open Spike.Lib.A64.Flow
open CoreLang CoreTerm

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`wc_waitLoop`'s limit load inside a state predicate `W`** with no
outside moves: `rtld_ndW` from a node `n` at the load's pc (the third
instruction after the stack check's label) to a node `nb` at the next pc;
`W` at `n`'s states (`hW`), the load's facts and the landing (`hedge`) are
the obligations. -/
theorem seg_waitTlsW {W : Frag isaLSE2} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {n nb : ND}
    (hpc : n.pc = (_root_.Executable.labels exe).label (WakeLabels.pfx ++ ".stack_check") + Int64.ofNat (4 * 2))
    (hF : FStable R F) (hW : ∀ s c, At exe endPc R F n s c → W s c)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (rAddr σ.regs .X10 8).toNat ∧ ms.mp ⟨rAddr σ.regs .X10 8, 8⟩ false ∧
      Mem.loadInt m.dmem (rAddr σ.regs .X10 8) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ ∀ v : Val, ms.G ⟨rAddr σ.regs .X10 8, 8⟩ v →
        Hit nb ⟨n.pc + Int64.ofNat 4, n.o.kill .X10, ldStep .X10 (v.setWidth 64) σ⟩ c') :
    SegW W (fun _ _ => False) p lbl ms (At exe endPc R F n) (At exe endPc R F nb) := by
  refine (rtld_ndW (N := fun _ : Unit => nb) (E := fun e : Empty => e.elim) hF
    (code_of hp hend wait_tlsCode hpc.symm) (fun s c hA => ⟨hW s c hA, fun _ h => h⟩)
    fun m σ c hA hD hJ => ?_).mono_post fun _ _ hn => ?_
  · obtain ⟨h1, h2, h3, c', hr, hL⟩ := hedge m σ c hA hD hJ
    exact ⟨h1, h2, h3, c', hr, fun v hv => .inl ⟨(), hL v hv⟩⟩
  · rcases hn with ⟨_, hb⟩ | ⟨e, _⟩
    · exact hb
    · exact e.elim

/-- **`wc_waitLoop`'s limit load from `x10 = tp` inside `TlsW`**
(`seg_waitTlsW`): the load's node `n` with `x10 = tp` (`hX`) and control
`c0` (`hc`), the limit word `tp + 8`'s facts with room up to `x9`'s address
`R.addr (-32)` (`hL`), the word not the flag's address `A` (`hA`), and the
landing node `nb` (at the next pc, offsets no stronger than `n`'s with `x10`
killed) holding after a load of a value within the room (`hJ`). The
predicate: off the exits and transfer sites (`abOff_at`), no load of `A`
(the state's only event is the load of `tp + 8`), control `c0`. -/
theorem seg_waitTlsLim (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) {n nb : ND}
    {tp A : BitVec 64} {c0 : Ctl}
    (hpc : n.pc = (_root_.Executable.labels exe).label (WakeLabels.pfx ++ ".stack_check") + Int64.ofNat (4 * 2))
    (hF : FStable R F) (hX : ∀ σ c, n.J σ c → σ.regs.X10.toBitVec = tp) (hc : ∀ σ c, n.J σ c → c = c0)
    (hL : Spike.Lib.A64.Flow.Ret0.LimOk ms F exe endPc (tp + 8#64) (R.addr (-32))) (hA : tp + 8#64 ≠ A)
    (hpcN : nb.pc = n.pc + Int64.ofNat 4) (ho : SO.le nb.o (n.o.kill .X10) = true)
    (hJ : ∀ σ c (v : Val), SORel R n.o σ.regs → n.J σ c → (v.setWidth 64).toNat ≤ (R.addr (-32)).toNat →
      nb.J (ldStep .X10 (v.setWidth 64) σ) c) :
    SegW (Spike.Lib.A64AbOffL.TlsW (_root_.Executable.labels exe).label A c0)
      (fun _ _ => False) p lbl ms (At exe endPc R F n) (At exe endPc R F nb) := by
  refine seg_waitTlsW hp hend hpc hF (fun s c hAt => ?_) fun m σ c hA hD hJn => ?_
  · obtain ⟨he, hn, hdc, hs, σ, hAb, hD, hJn⟩ := hAt
    refine ⟨abOff_at hp wait_tlsChk (k := 0) Nat.zero_lt_one he (by rw [hs, hpc, ofNat4_zero]),
      fun kl Lc k hex => ?_, hc σ c hJn⟩
    have hcell : CellAt s (ldrDir .X10 .X10 8) 4 :=
      (code_of hp hend wait_tlsCode hpc.symm s he hn).cell (j := 0) rfl rfl rfl (by rw [hs]; simp)
    have ha : rAddr s.st.1.regs .X10 8 = tp + 8#64 := by
      rw [hAb.regs]; exact Spike.Lib.A64.Flow.Ret0.rAddr_x10 (hX σ c hJn) 8
    have hl := exec_ldr_agrees hcell ha (by rw [← ha] at hL ⊢; exact ha ▸ hL.unmapped _ hD)
      (agrees_of_decls hdc _ _)
    rw [hl] at hex
    cases hex
    exact hA
  · have ha : rAddr σ.regs .X10 8 = tp + 8#64 := Spike.Lib.A64.Flow.Ret0.rAddr_x10 (hX σ c hJn) 8
    rw [ha]
    exact ⟨hL.rt, hL.mp, hL.unmapped m hD, c, .refl c, fun v hv =>
      ⟨hpcN, ho, hJ σ c v hA.so hJn (hL.room v hv)⟩⟩

end Tls

end Spike.Lib.A64.Flow.Worker.Wake.AbOffAt
