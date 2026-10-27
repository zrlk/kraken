/-
**`scc_rt_print`'s write system call from the output row** (AArch64):
`seg_printAW`'s given node `hsvc` (`Spike/Lib/A64PrintA.lean`), from the
segment the output row (`Out.emit`) gives one `svc` at a `write` to the
output.

The row's one-instruction segment is taken here as a hypothesis, `EmitW`,
of the shape the row's premises give (`EmitRow`): at a system call under the kernel model `Scc.Sem.A64.abi`
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

`hsvc_of_emit`: from `EmitW`, the source's byte steps from `P (k + j)` to
`P (k + j + 1)` at `buf0 + k + j`, `Q` of every `P`, and `Q` justifying
the abort, `scc_rt_print`'s `.svc` node is a segment to `.n5`: `Pw j :=
P (k + j)`, `Qw := Q k`, and each result is classified by `RC0` (`RetOk`
with `len0 < 2^63`).
-/
import Spike.Lib.A64PrintA

set_option linter.unusedSimpArgs false

namespace Spike.Lib.A64.PrintA

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64 Spike.Lib.A64.Flow
open Spike.Lib.A64.Print
open Scc.Sem.Kernel (writeRefused neg eintr eagain results)

/-! ## The output row -/

/-- **A result the kernel may return from a `write` after `j` bytes out**
(`Kernel.sysStep`): the count `j` if positive; with no byte out `-EINTR`,
`-EAGAIN` or a refusal. -/
abbrev RetOk (j : Nat) (r : BitVec 64) : Prop := Spike.Lib.WriteRetOk j r

/-- **The premises of the output row** at `(s, c)` into `X`, under the
kernel model `Scc.Sem.A64.abi`, the byte step `BO` and the abort's
justification `WE` (see the module docstring). -/
def EmitRow (p : Prog) (ms : MemSide isaLSE2) (BO : State → Nat → Ctl → (Ctl → Prop) → Prop)
    (WE : State → Ctl → Prop) (X : Frag isaLSE2) (s : State) (c : Ctl) : Prop :=
  ∃ (buf n : Nat) (Pw : Nat → Ctl → Prop) (Qw : Ctl → Prop),
    ms.K = some Scc.Sem.A64.abi ∧ Scc.Sem.A64.abi.atSys s = true ∧
    Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.write 1 buf n) ∧
    (∃ c', LocalRun p c c' ∧ Pw 0 c') ∧
    (∀ j < n, ∀ c1, Pw j c1 → BO s (buf + j) c1 (Pw (j + 1))) ∧
    (∀ j ≤ n, ∀ c1, Pw j c1 → ∀ r ∈ results (.write 1 buf n), RetOk j r →
      X (Scc.Sem.A64.abi.ret s r) c1 ∧ (j = 0 → writeRefused r = true → Qw c1)) ∧
    (∀ c1, Qw c1 → WE s c1)

/-- **The output row's one-instruction segment**, as a hypothesis: from every pair
of `A` inside `W`, not moved by `K`, at which the row's premises hold into
`X`, a segment to `X`. -/
def EmitW (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isaLSE2) (BO : State → Nat → Ctl → (Ctl → Prop) → Prop) (WE : State → Ctl → Prop) : Prop :=
  ∀ A X : Frag isaLSE2, (∀ s c, A s c → W s c ∧ ∀ s', ¬ K s s') → (∀ s c, A s c → EmitRow p ms BO WE X s c) →
    SegW W K p lbl ms A X

/-- **The output row's segment is a theorem** with the memory side's byte
step and abort justification (`BO := ms.bo`, `WE := ms.we`): `SegW.step` of
`Out.emit`. -/
theorem emitW_of_out {W : Frag isaLSE2} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} : EmitW W K p lbl ms ms.bo ms.we := by
  intro A X hW hrow
  refine SegW.step hW fun s c h => ?_
  obtain ⟨buf, n, Pw, Qw, hK, ha, hd, h0, hb, hr, hq⟩ := hrow s c h
  exact .emit Scc.Sem.A64.abi buf n Pw Qw hK ha hd h0 hb hr hq

/-! ## The classification of the result -/

/-- `-EINTR` and `-EAGAIN` are not small counts. -/
theorem neg_large {e : Nat} (h0 : 0 < e) (h : e < 2 ^ 63) : 2 ^ 63 ≤ (neg e).toNat := by
  simp only [neg, BitVec.toNat_neg, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : e < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  omega

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

section Svc

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {x29 ra buf0 : BitVec 64}
  {len0 : Nat} {P Q : Nat → Ctl → Prop}

/-- **`scc_rt_print`'s write system call is a segment inside `W`** from
`.svc` to `.n5`, from the output row's segment (`hE`, assumed), the
source's byte steps (`hbyte`: from `P (k + j)` to `P (k + j + 1)` by the
byte at `buf0 + k + j`, `k + j < len0`), `len0 < 2^63` wherever `P`
holds (`hlen`), `Q` of every `P` (`hPQ`: a refusal before any
byte of the call), and `Q` justifying the abort (`hwe`). The code is the
`svc` at `.svc` (`Print.Code.svc`). -/
theorem hsvc_of_emit {W : Frag isaLSE2} {K : State → State → Prop}
    {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop}
    (hE : EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (hlen : ∀ k c, P k c → len0 < 2 ^ 63)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).pc [svcDir])
    (hW : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc) s c →
      W s c ∧ ∀ s', ¬ K s s')
    (hPQ : ∀ k c, P k c → Q k c)
    (hbyte : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc) s c →
      ∀ k j c1, k + j < len0 → P (k + j) c1 → BO s ((buf0 + BitVec.ofNat 64 k).toNat + j) c1 (P (k + j + 1)))
    (hwe : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc) s c →
      ∀ k c1, Q k c1 → WE s c1) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc))
      (At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n5)) := by
  refine hE _ _ hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨k, hL, hk, hP⟩, h0, h8, h1, h2⟩ := id hAt
  obtain ⟨h16, h8', h48, h40, hkl⟩ := hL
  have hl := hlen k c hP
  have hc : CellAt s svcDir 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  have hx1 : s.st.1.regs.X1.toNat = (buf0 + BitVec.ofNat 64 k).toNat := by
    rw [hA.regs, ← h48, ← h1]; rfl
  have hx2 : s.st.1.regs.X2.toNat = len0 - k := by
    rw [hA.regs, UInt64.toNat, h2, h40, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hd : Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.write 1 (buf0 + BitVec.ofNat 64 k).toNat (len0 - k)) := by
    have hr0 : s.st.1.regs.X0 = 1 := by rw [hA.regs]; exact h0
    have hr8 : s.st.1.regs.X8 = 64 := by rw [hA.regs]; exact h8
    simp [Scc.Sem.A64.abi, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.a64, Scc.Sem.A64.xRegs, hr0, hr8, ← hx1,
      ← hx2]
  refine ⟨_, _, fun j c1 => P (k + j) c1, Q k, hK, Scc.Sem.A64.atSvc_of_cellAt hc, hd, ⟨c, .refl c, hP⟩,
    fun j hj c1 h => hbyte s c hAt k j c1 (by omega) h, fun j hj c1 hPj r _ hr => ⟨?_, fun hj0 _ => ?_⟩,
    fun c1 h => hwe s c hAt k c1 h⟩
  · rw [Scc.Sem.A64.abi_ret_of_cellAt hc r]
    have hA' : Flow.Abs R oI { s.st.1 with regs := { s.st.1.regs with X0 := UInt64.ofNat r.toNat } }
        (svcStep r σ) := by
      refine Flow.Abs.weaken (o' := oI) (o := oI.kill .X0) (by decide)
        ⟨by simp only [svcStep, hA.regs], hA.status, ?_, hA.slot⟩
      refine hA.so.kill .X0 fun r hr => ?_
      rcases r with y | _
      · cases y <;> first | rfl | exact absurd rfl hr
      · rfl
    have hD' : F { s.st.1 with regs := { s.st.1.regs with X0 := UInt64.ofNat r.toNat } } :=
      hF _ _ hD fun _ _ _ => rfl
    refine ⟨he, hn, hdc, ?_, svcStep r σ, hA', hD', k, ⟨h16, h8', h48, h40, hkl⟩, ?_⟩
    · simp only [svcRet, after, hpc]; rfl
    · have hx0 : (svcStep r σ).regs.X0.toBitVec = r := by simp [svcStep]
      rw [hx0]
      exact rc0_of_retOk (hlen _ _ hPj) hj (hPQ k c1) hPj hr
  · subst hj0; exact hPQ k c1 hPj

end Svc

end Spike.Lib.A64.PrintA
