/-
**`hello1.w`'s x86-64 write tail from `print`'s `write` call** (the x64 half
of `PrintWrDt`): `scc_rt_print`'s write tail inside its frame
(`Spike/Lib/Rt/X64PrintDt.lean`), on through its return, `wc_main`'s
return and `scc_rt_main`'s `exit_group` (`Spike/Lib/Rt/X64Hello1RetDt.lean`),
or through its abort call, the dispatcher and the `write` stub
(`Spike/Lib/Rt/X64Hello1AbDt.lean`) into the stub's tail
(`Spike/Lib/Rt/X64StubDt.lean`). The regions are `hello1.w`'s:
`scc_rt_main`'s `R0`, `wc_main`'s `wR R0`, `print`'s `pR (wR R0)`,
`scc_rt_abort`'s `aR R0`, for some `R0` (`PrintDt` is a predicate of the
state alone).

- `PrintDt exe endPc`: for some `R0` (`OK`, `R0.lo ≤ -256`, `0 ≤ R0.hi`),
  `print`'s pieces (the caller's `%rbp` `wc_main`'s frame pointer, the
  return address `.x15`, under `CP`), `RetDt` or `AbIn`; or the `write`
  stub's `StubDt`;
- `printDt_closed`: closed under certification, given the code (`Print.Code`,
  `Abort.Disp.Code`, the `write` stub's `Abort.Code`, `wc_main`'s `.x15`
  block, `scc_rt_main`'s `exit_group` tail) and `PrintDt` off the transfer
  sites (`hns`);
- `printDt_of_at`: `print`'s `write` node (`At … (Print.N … .sys)` in
  `pR (wR R0)`, a frame condition giving `CP`, the ghost `%rbp` `wc_main`'s
  frame pointer) is in `PrintDt`;
- `printDt_closed_hello1`: `printDt_closed` in any valid layout of
  `hello1Cells`, the code from its checks.
-/
import Spike.Lib.Rt.X64Hello1AbDt
import Spike.Lib.X64Hello1Segs
import Scc.Cert.Rt.X64Abort
import Scc.Cert.Rt.X64Print

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem
open Scc.Sem.X64 (abi)
open Spike.Lib.X64
open Spike.Lib (ClosedC StepsTo)
open Spike.Lib.X64.Flow.Hello1 (wcR15 wR pR)
open Scc.Cert.Rt.X64 (Lays endOf code_field)

/-- **`hello1.w`'s write tail from `print`'s `write` call.** -/
def PrintDt (exe : _root_.Executable) (endPc : Int64) (s : State) : Prop :=
  (∃ R0 : Region, R0.OK ∧ R0.lo ≤ -256 ∧ 0 ≤ R0.hi ∧
    (PrintIn exe endPc (pR (wR R0)) ((wR R0).addr (-8))
        ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec (CP exe R0) s ∨
      RetDt exe endPc R0 s ∨ AbIn exe endPc (aR R0) s)) ∨
  StubDt exe endPc (_root_.Executable.labels exe).label Abort.write s

section Closed

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64}

/-- **`hello1.w`'s write tail is closed under certification**, given the
code it runs through and the tail off the transfer sites. -/
theorem printDt_closed {c0 c1 c2 : Ctl} {rbp0 ra : BitVec 64} (hpc : Print.Code c0 rbp0 ra exe endPc)
    (hdc : Abort.Disp.Code c1 exe endPc) (hsc : Abort.Code Abort.write c2 Abort.x1Write exe endPc)
    (hc15 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label ".Lwc_main.x15") wcR15)
    (hcx : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label ".Lscc_rt_main.x3") (Flow.xExit (-48) 4 4 5))
    (hcs : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pcX exe) [(op64 .syscall, 2)])
    (hns : ∀ s, PrintDt exe endPc s → Kernel.siteAt abi μ s = none) (x : Kernel.KState) :
    ClosedC Arch.tso (Kernel.certSem abi Arch.tso μ x 0) 0 (PrintDt exe endPc) := by
  have hSD : ClosedC Arch.tso (Kernel.certSem abi Arch.tso μ x 0) 0
      (StubDt exe endPc (_root_.Executable.labels exe).label Abort.write) :=
    stubDt_closed hsc rfl (fun s h => hns s (.inr h)) x
  have hG : ∀ R0 : Region, R0.OK → R0.lo ≤ -256 → 0 ≤ R0.hi →
      ClosedC Arch.tso (Kernel.certSem abi Arch.tso μ x 0) 0 (fun s =>
        PrintIn exe endPc (pR (wR R0)) ((wR R0).addr (-8))
          ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec (CP exe R0) s ∨
        RetDt exe endPc R0 s ∨ AbIn exe endPc (aR R0) s ∨
        StubDt exe endPc (_root_.Executable.labels exe).label Abort.write s) := by
    intro R0 hR hlo hhi
    have hin : ∀ {D : State → Prop}, (∀ s, D s → RetDt exe endPc R0 s ∨ AbIn exe endPc (aR R0) s ∨
        PrintIn exe endPc (pR (wR R0)) ((wR R0).addr (-8))
          ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec (CP exe R0) s) →
        ∀ s, D s → Kernel.siteAt abi μ s = none := fun hD s h => hns s (.inl ⟨R0, hR, hlo, hhi, by
          rcases hD s h with h | h | h
          · exact .inr (.inl h)
          · exact .inr (.inr h)
          · exact .inl h⟩)
    have hW := wR_ok hR (by omega) hhi
    refine ClosedC.rel (printIn_steps (Out := fun s => RetDt exe endPc R0 s ∨ AbIn exe endPc (aR R0) s ∨
        StubDt exe endPc (_root_.Executable.labels exe).label Abort.write s) hpc
        (Region.callee_ok hW (by simp [Region.callee]) (by decide) (by simp [Region.callee])
          (by simp [Region.callee]))
        (by simp [Region.callee]) (by simp [Region.callee]) (cp_stable hR (by omega) hhi)
        (hin fun _ h => .inr (.inr h))
        (fun σ0 hJ s m he hn hA hC => .inl (retDt_of_ret σ0 hJ s m he hn hA hC))
        (fun σ0 _ s m he hn hA hC => .inr (.inl (abIn_of_fail hlo hhi σ0 s m he hn hA hC))))
      (ClosedC.union (retDt_closed hR (by omega) hhi hc15 hcx hcs (hin fun _ h => .inl h))
        (ClosedC.rel (abIn_steps hdc hsc (aR_ok hR hlo hhi) (by simp [Region.callee])
          (by simp [Region.callee]) (hin fun _ h => .inr (.inl h))) hSD))
  rintro p q (⟨R0, hR, hlo, hhi, h⟩ | h) hs
  · obtain ⟨hq, hpr⟩ := hG R0 hR hlo hhi p q (by
      rcases h with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))) hs
    refine ⟨?_, hpr⟩
    rcases hq with h | h | h | h
    · exact .inl ⟨R0, hR, hlo, hhi, .inl h⟩
    · exact .inl ⟨R0, hR, hlo, hhi, .inr (.inl h)⟩
    · exact .inl ⟨R0, hR, hlo, hhi, .inr (.inr h)⟩
    · exact .inr h
  · exact (hSD p q h hs).imp_left Or.inr

end Closed

/-- **`print`'s `write` node is in the tail**: in `print`'s region
`pR (wR R0)`, under a frame condition giving `CP`, the ghost `%rbp`
`wc_main`'s frame pointer and the return address `.x15`. -/
theorem printDt_of_at {exe : _root_.Executable} {endPc : Int64} {R0 : Region} {F : MachineData → Prop}
    {c0 c : Ctl} {rbp0 : BitVec 64} {s : State} (hR : R0.OK) (hlo : R0.lo ≤ -256) (hhi : 0 ≤ R0.hi)
    (hF : ∀ m, F m → CP exe R0 m) (hrbp : rbp0 = (wR R0).addr (-8))
    (hAt : At exe endPc (pR (wR R0)) F (Print.N (_root_.Executable.labels exe).label c0 rbp0
      ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec .sys) s c) :
    PrintDt exe endPc s := by
  subst hrbp
  obtain ⟨he, hn, -, hpc, σ, hA, hD, ⟨-, h0, h8⟩, h1, h2⟩ := hAt
  exact .inl ⟨R0, hR, hlo, hhi, .inl (.inr (.inr (.inr (.inl ⟨he, hn, hpc, σ, ⟨h0, h8⟩, h1, h2, hA, hF _ hD⟩))))⟩

section Hello1

variable {μ : Marks} {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}

/-- **`hello1.w`'s write tail is closed under certification** in any valid
layout of `hello1Cells`: `printDt_closed`, the code from the cells' checks
(`hello1_print`, `hello1_abort`, `hello1_wcBodyIn`, `hello1_mainExit`; `c0` any control, the code
facts' ghost). -/
theorem printDt_closed_hello1 (c0 : Ctl) (hp : Lays exe SccCode.hello1Cells)
    (hend : endPc = endOf exe SccCode.hello1Cells)
    (hns : ∀ s, PrintDt exe endPc s → Kernel.siteAt abi μ s = none) (x : Kernel.KState) :
    ClosedC Arch.tso (Kernel.certSem abi Arch.tso μ x 0) 0 (PrintDt exe endPc) := by
  have off0 := Scc.Cert.Rt.X64.Print.off0
  have hpr := SccCode.hello1_print
  simp only [Scc.Cert.Rt.X64.Print.printIn, Bool.and_eq_true, and_assoc] at hpr
  obtain ⟨h0, h1, h2, h3, h4, hs, h5, h6, h7, h8, h9, h10, h11, h12, h13, -⟩ := hpr
  have hpc : Print.Code c0 0 0 exe endPc :=
    ⟨code_field hp hend h0 (off0 _), code_field hp hend h1 (off0 _), code_field hp hend h2 (off0 _),
      code_field hp hend h3 rfl, code_field hp hend h4 (off0 _), code_field hp hend h5 rfl,
      code_field hp hend h6 rfl, code_field hp hend h7 (off0 _),
      code_field hp hend h8 rfl, code_field hp hend h9 (off0 _), code_field hp hend h10 rfl,
      code_field hp hend h11 (off0 _), code_field hp hend h12 (off0 _), code_field hp hend h13 (off0 _),
      code_field hp hend hs rfl⟩
  have hab := SccCode.hello1_abort
  have hdc : Abort.Disp.Code c0 exe endPc := by
    simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hab
    exact Scc.Cert.Rt.X64.Abort.code_disp hp hend hab.2
  have hsc : Abort.Code Abort.write c0 Abort.x1Write exe endPc :=
    Scc.Cert.Rt.X64.Abort.code_stubs hp hend hab .write
  have hwc := Flow.Hello1.hello1_wcBodyIn
  simp only [Flow.Hello1.wcBodyIn, Bool.and_eq_true] at hwc
  have hmx := Flow.hello1_mainExit
  simp only [Flow.exitIn, Bool.and_eq_true] at hmx
  refine printDt_closed hpc hdc hsc (code_field hp hend hwc.1.2 (off0 _))
    (code_field hp hend hmx.1 (off0 _))
    (code_field hp hend hmx.2 ?_) hns x
  show _ + Int64.ofNat (4 + 4 + 5) = _ + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5
  rw [Int64.add_assoc, Int64.add_assoc]; rfl

end Hello1

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.X64.Rt.printDt_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms printDt_closed

/--
info: 'Spike.Lib.X64.Rt.printDt_of_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms printDt_of_at

/--
info: 'Spike.Lib.X64.Rt.printDt_closed_hello1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms printDt_closed_hello1

end Spike.Lib.X64.Rt
