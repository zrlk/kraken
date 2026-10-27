/-
**`scc_rt_print`'s write system call from the output row** (x64):
`seg_printAW`'s given node `hsys` (`Spike/Lib/X64PrintA.lean`), from the
segment the output row (`Out.emit`) gives one `syscall` at a `write` to the
output: the x64 twin of `Spike/Lib/A64PrintEmit.lean`.

The row's one-instruction segment is taken here as a hypothesis, `EmitW`,
of the shape the row's premises give (`EmitRow`): at a system call under the kernel model `Scc.Sem.X64.abi`
decoding to `write(1, buf, n)`,

- the source runs locally to `Pw 0`;
- each byte `j < n` moves the source from `Pw j` to `Pw (j + 1)` by one
  output (`BO s (buf + j)`, the row's byte step, kept abstract);
- every result `r` the kernel may return after `j ≤ n` bytes (`RetOk j r`,
  `Kernel.sysStep`'s `write` returns) lands in the exit with the source at
  `Pw j`, and a refusal with no byte out holds `Qw`;
- `Qw` justifies the abort (`WE`, the row's justification, kept abstract).

`EmitW` is what `SegW.step` makes of the row with `BO := ms.bo` and
`WE := ms.we`: `emitW_of_out` (`RetOk` is `Spike.Lib.WriteRetOk`).

`hsys_of_emit`: from `EmitW`, the source's byte steps from `P (k + j)` to
`P (k + j + 1)` at `buf0 + k + j`, `Q` of every `P`, and `Q` justifying
the abort, `scc_rt_print`'s `.sys` node is a segment to `.n5`: `Pw j :=
P (k + j)`, `Qw := Q k`, and each result is classified by `RC0` (`RetOk`
with `len0 < 2^63`). The `syscall` also writes `%rcx` and `%r11`, which no
invariant past it reads.
-/
import Spike.Lib.X64PrintA
import Spike.Lib.X64Nodes

set_option linter.unusedSimpArgs false

namespace Spike.Lib.X64.PrintA

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64 Spike.Lib.X64
open Spike.Lib.X64.Print (PN oI pcSys)
open Scc.Sem.Kernel (writeRefused neg eintr eagain results)

/-! ## The output row -/

/-- **A result the kernel may return from a `write` after `j` bytes out**
(`Kernel.sysStep`): the count `j` if positive; with no byte out `-EINTR`,
`-EAGAIN` or a refusal. -/
abbrev RetOk (j : Nat) (r : BitVec 64) : Prop := Spike.Lib.WriteRetOk j r

/-- **The premises of the output row** at `(s, c)` into `X`, under the
kernel model `Scc.Sem.X64.abi`, the byte step `BO` and the abort's
justification `WE` (see the module docstring). -/
def EmitRow (p : Prog) (ms : MemSide isa) (BO : State → Nat → Ctl → (Ctl → Prop) → Prop)
    (WE : State → Ctl → Prop) (X : Frag isa) (s : State) (c : Ctl) : Prop :=
  ∃ (buf n : Nat) (Pw : Nat → Ctl → Prop) (Qw : Ctl → Prop),
    ms.K = some Scc.Sem.X64.abi ∧ Scc.Sem.X64.abi.atSys s = true ∧
    Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
      some (.write 1 buf n) ∧
    (∃ c', LocalRun p c c' ∧ Pw 0 c') ∧
    (∀ j < n, ∀ c1, Pw j c1 → BO s (buf + j) c1 (Pw (j + 1))) ∧
    (∀ j ≤ n, ∀ c1, Pw j c1 → ∀ r ∈ results (.write 1 buf n), RetOk j r →
      X (Scc.Sem.X64.abi.ret s r) c1 ∧ (j = 0 → writeRefused r = true → Qw c1)) ∧
    (∀ c1, Qw c1 → WE s c1)

/-- **The output row's one-instruction segment**, as a hypothesis: from every pair
of `A` inside `W`, not moved by `K`, at which the row's premises hold into
`X`, a segment to `X`. -/
def EmitW (W : Frag isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isa) (BO : State → Nat → Ctl → (Ctl → Prop) → Prop) (WE : State → Ctl → Prop) : Prop :=
  ∀ A X : Frag isa, (∀ s c, A s c → W s c ∧ ∀ s', ¬ K s s') → (∀ s c, A s c → EmitRow p ms BO WE X s c) →
    SegW W K p lbl ms A X

/-- **The output row's segment is a theorem** with the memory side's byte
step and abort justification (`BO := ms.bo`, `WE := ms.we`): `SegW.step` of
`Out.emit`. -/
theorem emitW_of_out {W : Frag isa} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} : EmitW W K p lbl ms ms.bo ms.we := by
  intro A X hW hrow
  refine SegW.step hW fun s c h => ?_
  obtain ⟨buf, n, Pw, Qw, hK, ha, hd, h0, hb, hr, hq⟩ := hrow s c h
  exact .emit Scc.Sem.X64.abi buf n Pw Qw hK ha hd h0 hb hr hq

/-! ## The classification of the result -/

/-- **A result the kernel may return is one `RC0` admits**, the source at
`P (k + j)` after `j ≤ len0 - k` bytes. -/
theorem rc0_of_retOk {len0 k j : Nat} {P Q : Nat → Ctl → Prop} {r : BitVec 64} {c : Ctl} (hlen : len0 < 2 ^ 63)
    (hj : j ≤ len0 - k) (hPQ : P k c → Q k c) (hP : P (k + j) c) (hr : RetOk j r) : RC0 len0 P Q k r c := by
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · rcases hr.2 rfl with h | h | h
    · exact .inl ⟨h.trans c4_eq.symm, hP⟩
    · exact .inr (.inl ⟨h.trans c11_eq.symm, hP⟩)
    · exact .inr (.inr (.inr ⟨h, hPQ hP⟩))
  · have hr' := hr.1 hpos
    have hn : r.toNat = j := by rw [hr', BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    exact .inr (.inr (.inl ⟨by omega, by omega, by rw [hn]; exact hP⟩))

/-! ## The system call -/

section Sys

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {rbp0 ra buf0 : BitVec 64}
  {len0 : Nat} {P Q : Nat → Ctl → Prop}

/-- **`scc_rt_print`'s write system call is a segment inside `W`** from
`.sys` to `.n5`, from the output row's segment (`hE`, assumed), the
source's byte steps (`hbyte`: from `P (k + j)` to `P (k + j + 1)` by the
byte at `buf0 + k + j`, `k + j < len0`), `len0 < 2^63` wherever `P`
holds (`hlen`), `Q` of every `P` (`hPQ`: a refusal before any
byte of the call), and `Q` justifying the abort (`hwe`). The code is the
`syscall` at `.sys` (`Print.Code.sys`). -/
theorem hsys_of_emit {W : Frag isa} {K : State → State → Prop}
    {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop}
    (hE : EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (hlen : ∀ k c, P k c → len0 < 2 ^ 63)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys).pc
        [(.instr (.regular .W64 .W64 .syscall), 2)])
    (hW : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys) s c →
      W s c ∧ ∀ s', ¬ K s s')
    (hPQ : ∀ k c, P k c → Q k c)
    (hbyte : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys) s c →
      ∀ k j c1, k + j < len0 → P (k + j) c1 → BO s ((buf0 + BitVec.ofNat 64 k).toNat + j) c1 (P (k + j + 1)))
    (hwe : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys) s c →
      ∀ k c1, Q k c1 → WE s c1) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys))
      (At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n5)) := by
  refine hE _ _ hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨k, hL, hk, hP⟩, hdi, hax, hsi, hdx⟩ := id hAt
  obtain ⟨h0, h8, h16, h24, hkl⟩ := hL
  have hl := hlen k c hP
  have hc : CellAt s (.instr (.regular .W64 .W64 .syscall)) 2 := (hcode s he hn).cell0 rfl rfl hpc
  have hrax : s.st.1.regs.rax.toNat = 1 := by
    have : s.st.1.regs.get64 .rax = 1 := by rw [hA.regs]; exact hax
    simp only [Reg64s.get64] at this; rw [UInt64.toNat, this]; rfl
  have hrdi : s.st.1.regs.rdi.toNat = 1 := by
    have : s.st.1.regs.get64 .rdi = 1 := by rw [hA.regs]; exact hdi
    simp only [Reg64s.get64] at this; rw [UInt64.toNat, this]; rfl
  have hrsi : s.st.1.regs.rsi.toNat = (buf0 + BitVec.ofNat 64 k).toNat := by
    have : s.st.1.regs.get64 .rsi = buf0 + BitVec.ofNat 64 k := by rw [hA.regs, hsi, h16]
    simp only [Reg64s.get64] at this; rw [UInt64.toNat, this]
  have hrdx : s.st.1.regs.rdx.toNat = len0 - k := by
    have : s.st.1.regs.get64 .rdx = BitVec.ofNat 64 (len0 - k) := by rw [hA.regs, hdx, h24]
    simp only [Reg64s.get64] at this; rw [UInt64.toNat, this, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hd : Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
      some (.write 1 (buf0 + BitVec.ofNat 64 k).toNat (len0 - k)) := by
    simp [Scc.Sem.X64.abi, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64, hrax, hrdi, hrsi, hrdx]
  refine ⟨_, _, fun j c1 => P (k + j) c1, Q k, hK, Scc.Sem.X64.atSyscall_of_cellAt hc, hd, ⟨c, .refl c, hP⟩,
    fun j hj c1 h => hbyte s c hAt k j c1 (by omega) h, fun j hj c1 hPj r _ hr => ⟨?_, fun hj0 _ => ?_⟩,
    fun c1 h => hwe s c hAt k c1 h⟩
  · rw [Scc.Sem.X64.abi_ret_of_cellAt hc r]
    let pc' := (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys).pc + Int64.ofNat 2
    have hA' : Abs R oI { s.st.1 with regs := syscallRegs pc' (Scc.Sem.X64.rflags σ.status) r s.st.1.regs }
        (syscallStep pc' r σ) :=
      Abs.weaken (o := syscallSO oI) (by decide)
        ⟨by simp only [syscallStep, hA.regs], hA.zmms, hA.status, syscallSO_rel hA.so _ _ _, hA.slot⟩
    have hD' : F { s.st.1 with regs := syscallRegs pc' (Scc.Sem.X64.rflags σ.status) r s.st.1.regs } :=
      hF _ _ hD fun _ _ _ => rfl
    have hs1 : syscallRet s 2 (Scc.Sem.X64.kret (Scc.Sem.X64.rflags s.st.1.status) (syscallInfo s 2) r) =
        { s with st := ({ s.st.1 with regs := syscallRegs pc' (Scc.Sem.X64.rflags σ.status) r s.st.1.regs },
          pc') } := by
      simp only [syscallRet, after, Scc.Sem.X64.kret, syscallRegs, hpc, hA.status, pc']
    rw [hs1]
    refine ⟨he, hn, hdc, ?_, syscallStep pc' r σ, hA', hD', k, ⟨h0, h8, h16, h24, hkl⟩, ?_⟩
    · show pc' = _
      simp only [pc', N, pcSys, Int64.add_assoc]; rfl
    · have hx0 : (syscallStep pc' r σ).regs.get64 .rax = r := by
        simp [syscallStep, syscallRegs, Reg64s.get64]
      rw [hx0]
      exact rc0_of_retOk (hlen _ _ hPj) hj (hPQ k c1) hPj hr
  · subst hj0; exact hPQ k c1 hPj

end Sys

end Spike.Lib.X64.PrintA
