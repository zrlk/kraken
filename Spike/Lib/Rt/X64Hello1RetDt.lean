/-
**`hello1.w`'s write tail after `scc_rt_print` returns** (x86-64): from
`print`'s return (`Print.x13`'s `ret`, at `wc_main`'s `.x15` with `%rsp`
past the return address in `print`'s region), `wc_main`'s `.x15` block
(`%rax = 0`, the epilogue, `ret` to `scc_rt_main`'s `.x3`), and
`scc_rt_main`'s `exit_group` tail (`xExit`, then the `syscall`), the states
step among themselves under the certification steps and stop at the
`exit_group` call (`ClosedC`). The pieces are `Spike/Lib/Rt/X64TailDt.lean`'s,
each in its function's region, with a frame condition carrying the callers'
cells outside it (`CallerCells`) and, in `wc_main`'s region, its saved
return address and `%rbp` (`WcRa`, `WcFp`).

- `cell_kept`, `callerCells_stable`: a caller's cell outside a callee's
  region survives a write inside it;
- `abs_leave_cells`: leaving a callee's region with the caller's cells
  outside it holding values (`at_leave` with the caller's abstract state
  read off the memory);
- `Abs.add_rbp`, `Abs.drop_regs`: adding `%rbp`'s offset from its value,
  forgetting the registers' offsets;
- `RetDt exe endPc R0`: `wc_main`'s `.x15` block in its region `wR R0`,
  `scc_rt_main`'s `exit_group` tail in its region `R0`, the `exit_group`
  call; `retDt_closed`: closed under certification, given the blocks'
  code and the pieces off the transfer sites;
- `retDt_of_ret`: `print`'s return lands in `RetDt` (the `hret` of
  `printIn_steps` for `print`'s region `pR (wR R0)`).
-/
import Spike.Lib.Rt.X64PrintDt
import Spike.Lib.Rt.X64WcRa
import Spike.Lib.X64Hello1Main

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem
open Scc.Sem.X64 (abi)
open Spike.Lib.X64
open Spike.Lib (ClosedC StepsTo upd upd_apply)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Flow.Hello1 (wcR15 wcR15_run wcR15_ok oB mO wR pR)

/-! ## Crossing a callee's region -/

section Cross

variable {R : Region} {kc lo' hi' : Int}

/-- **A caller's cell outside the callee's region survives a write inside
it.** -/
theorem cell_kept {k : Int} {m m' : MachineData} (hR : R.OK) (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0)
    (hkc : kc < R.hi) (hk8 : kc % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0) (hk : R.Off k)
    (hn : ¬ (R.callee kc lo' hi').Off (k - kc)) (hd : DFrame (R.callee kc lo' hi') m m') :
    Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt m.dmem (R.addr k) 8 :=
  hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkc hk8 hl8 hh8 hk hn)

/-- **The caller's cells outside the callee's region hold values** under
every write inside it. -/
theorem callerCells_stable (hR : R.OK) (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi)
    (hk8 : kc % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0) :
    FStable (R.callee kc lo' hi') (CallerCells R kc lo' hi') := fun _ _ hm hd k hk hn => by
  rw [cell_kept hR hlo hlo0 hkc hk8 hl8 hh8 hk hn hd]; exact hm k hk hn

/-- The caller's abstract state read off the memory: the callee's
registers, the region's cells' values. -/
def cellsAS (R : Region) (m : MachineData) (σx : AS) : AS :=
  { σx with slot := fun k => BitVec.ofInt 64 ((Mem.loadInt m.dmem (R.addr k) 8).getD 0) }

/-- **Leaving the callee's region with the caller's cells holding values**:
machine data related to `σx` at `⟨e, []⟩` in the callee's region at `kc`,
the caller's cells outside it holding values, is related at `⟨kc + e, []⟩`
in the caller's region to the state the caller's left, the caller's cells
read off the memory. -/
theorem abs_leave_cells {e : Int} {m : MachineData} {σx : AS}
    (hAx : Abs (R.callee kc lo' hi') ⟨e, []⟩ m σx) (hC : CallerCells R kc lo' hi' m) :
    Abs R ⟨kc + e, []⟩ m (leave (R.callee kc lo' hi') kc (cellsAS R m σx) σx) := by
  refine ⟨hAx.regs, hAx.zmms, hAx.status, ?_, fun k hk => ?_⟩
  · intro r k' hr
    obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
    have := hAx.so .rsp e (by simp [SO.get])
    simp only [leave] at this ⊢
    rw [this, Region.callee_addr]
  · by_cases hin : (R.callee kc lo' hi').Off (k - kc)
    · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
      refine ⟨j, ?_, ?_⟩
      · rw [Region.callee_addr, show kc + (k - kc) = k by omega] at hj; exact hj
      · simp only [leave]; rw [ite_eq_left hin]; exact hv
    · obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (hC k hk hin)
      refine ⟨j, hj, ?_⟩
      simp only [leave, cellsAS]; rw [ite_eq_right hin, hj]; rfl

/-- **A caller's cell read off the memory** outside the callee's region. -/
theorem leave_cellsAS_slot {m : MachineData} {σx : AS} {k j : Int}
    (hn : ¬ (R.callee kc lo' hi').Off (k - kc)) (hj : Mem.loadInt m.dmem (R.addr k) 8 = some j) :
    (leave (R.callee kc lo' hi') kc (cellsAS R m σx) σx).slot k = BitVec.ofInt 64 j := by
  simp only [leave, cellsAS]; rw [ite_eq_right hn, hj]; rfl

end Cross

/-- **`%rbp`'s offset from its value**: machine data related at offsets
with `%rsp` alone is related at `%rbp` at `k` too, `%rbp` being `R.addr k`. -/
theorem Abs.add_rbp {R : Region} {sp k : Int} {m : MachineData} {σ : AS} (hA : Abs R ⟨sp, []⟩ m σ)
    (hb : σ.regs.get64 .rbp = R.addr k) : Abs R ⟨sp, [(.rbp, k)]⟩ m σ := by
  refine ⟨hA.regs, hA.zmms, hA.status, fun r k' hk => ?_, hA.slot⟩
  unfold SO.get at hk
  split at hk
  · rename_i hr; subst hr; cases hk; exact hA.so .rsp sp (SO.get_rsp _)
  · simp only [lk] at hk
    split at hk
    · rename_i hb'; subst hb'; cases hk; exact hb
    · simp at hk

/-- **Forgetting the registers' offsets.** -/
theorem Abs.drop_regs {R : Region} {sp : Int} {rs : List (Reg64 × Int)} {m : MachineData} {σ : AS}
    (hA : Abs R ⟨sp, rs⟩ m σ) : Abs R ⟨sp, []⟩ m σ := by
  refine ⟨hA.regs, hA.zmms, hA.status, fun r k hk => ?_, hA.slot⟩
  obtain ⟨rfl, rfl⟩ := SO.get_sp_only hk
  exact hA.so .rsp _ (SO.get_rsp _)

/-! ## The pieces -/

section Pieces

variable (exe : _root_.Executable) (endPc : Int64) (R0 : Region)

/-- **`wc_main`'s frame at `.x15`**: the return address `scc_rt_main`'s
`.x3`, the saved `%rbp` `scc_rt_main`'s (`R0.addr (-8)`). -/
def WJ (σ : AS) : Prop :=
  Int64.ofBitVec (σ.slot 0) = (_root_.Executable.labels exe).label ".Lscc_rt_main.x3" ∧ σ.slot (-8) = R0.addr (-8)

/-- **`print`'s frame condition** in `hello1.w`: the callers' cells outside
their callees' regions hold values (`scc_rt_main`'s outside `wc_main`'s,
`wc_main`'s outside `print`'s), `wc_main`'s return address and saved
`%rbp` (the shape of the frame condition `hello1_main_x2_segW`'s `hsvc`
hands `print`'s `write`, without the caller's `F`). -/
def CP (m : MachineData) : Prop :=
  (CallerCells R0 (-80) (-144) 8 m ∧ CallerCells (wR R0) (-96 - 8) (-40) 16 m) ∧
    WcRa (wR R0) ((_root_.Executable.labels exe).label ".Lscc_rt_main.x3") m ∧ WcFp (wR R0) (R0.addr (-8)) m

/-- The `exit_group` call's pc: after `xExit`'s three instructions. -/
abbrev pcX : Int64 :=
  (_root_.Executable.labels exe).label ".Lscc_rt_main.x3" + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5

/-- **After `print`'s return**: `wc_main`'s `.x15` block in its region,
`scc_rt_main`'s `exit_group` tail in its region, the `exit_group` call. -/
def RetDt (s : State) : Prop :=
  BlkSt exe endPc (wR R0) ((_root_.Executable.labels exe).label ".Lwc_main.x15") oB wcR15 (WJ exe R0)
    (CallerCells R0 (-80) (-144) 8) s ∨
  BlkSt exe endPc R0 ((_root_.Executable.labels exe).label ".Lscc_rt_main.x3") mO (Flow.xExit (-48) 4 4 5)
    (fun _ => True) (fun _ => True) s ∨
  ExitSt exe endPc (pcX exe) s

end Pieces

section Steps

variable {A : Arch} {μ : Marks} {x : Kernel.KState} {tid : Nat}
  {exe : _root_.Executable} {endPc : Int64} {R0 : Region}

/-- `wc_main`'s region is fine. -/
theorem wR_ok (hR : R0.OK) (hlo : R0.lo ≤ -224) (hhi : 0 ≤ R0.hi) : (wR R0).OK :=
  Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)

/-- A region bound of a callee's region. -/
local macro "rg" : tactic => `(tactic| simp [Region.callee])

set_option linter.unusedSimpArgs false in
/-- **`print`'s frame condition survives writes inside `print`'s region.** -/
theorem cp_stable (hR : R0.OK) (hlo : R0.lo ≤ -224) (hhi : 0 ≤ R0.hi) :
    FStable (pR (wR R0)) (CP exe R0) := by
  have hW := wR_ok hR hlo hhi
  have h1 : FStable (wR R0) (CallerCells R0 (-80) (-144) 8) :=
    callerCells_stable hR (by omega) (by rg) (by omega) (by rg) (by rg) (by rg)
  have h1' := FStable.callee (kc := -96 - 8) (lo' := -40) (hi' := 16) hW (by rg) (by rg) (by rg)
    (by rg) h1
  have h2 : FStable (pR (wR R0)) (CallerCells (wR R0) (-96 - 8) (-40) 16) :=
    callerCells_stable hW (by rg) (by rg) (by rg) (by rg) (by rg) (by rg)
  have hk : ∀ {k : Int} {m m'}, (wR R0).Off k → ¬ (pR (wR R0)).Off (k - (-96 - 8)) →
      DFrame (pR (wR R0)) m m' → Mem.loadInt m'.dmem ((wR R0).addr k) 8 = Mem.loadInt m.dmem ((wR R0).addr k) 8 :=
    fun hk hn hd => cell_kept hW (by rg) (by rg) (by rg) (by rg) (by rg) (by rg) hk hn hd
  rintro m m' ⟨⟨c1, c2⟩, ⟨j, hj, hv⟩, ⟨j', hj', hv'⟩⟩ hd
  refine ⟨⟨h1' m m' c1 hd, h2 m m' c2 hd⟩, ⟨j, ?_, hv⟩, ⟨j', ?_, hv'⟩⟩
  · rw [hk (by simp [Region.Off, Region.callee]) (by simp [Region.Off, Region.callee]) hd]; exact hj
  · rw [hk (by simp [Region.Off, Region.callee]) (by simp [Region.Off, Region.callee]) hd]; exact hj'

/-- **`print`'s return lands after it**: `x13`'s run from `print`'s frame
(the caller's `%rbp` `wc_main`'s frame pointer, the return address
`.x15`) under `print`'s frame condition is `wc_main`'s `.x15` block's entry
in its region (the `hret` of `printIn_steps`). -/
theorem retDt_of_ret (σ0 : AS) (hJ : PJ ((wR R0).addr (-8))
      ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec σ0)
    (s : State) (m : MachineData) (he : s.exe = exe) (hn : s.endPc = endPc)
    (hA : Abs (pR (wR R0)) (arun (_root_.Executable.labels exe).label Print.x13
        ⟨(_root_.Executable.labels exe).label ".Lscc_rt_print.done", Print.oI, σ0⟩).so m
      (arun (_root_.Executable.labels exe).label Print.x13
        ⟨(_root_.Executable.labels exe).label ".Lscc_rt_print.done", Print.oI, σ0⟩).σ)
    (hC : CP exe R0 m) :
    RetDt exe endPc R0 { s with st := (m, (arun (_root_.Executable.labels exe).label Print.x13
      ⟨(_root_.Executable.labels exe).label ".Lscc_rt_print.done", Print.oI, σ0⟩).pc) } := by
  obtain ⟨h0, h8⟩ := hJ
  obtain ⟨⟨c1, c2⟩, ⟨j, hj, hv⟩, ⟨j', hj', hv'⟩⟩ := hC
  rw [Print.x13_run] at hA ⊢
  have hL := abs_leave_cells hA c2
  rw [show (-96 - 8 : Int) + 16 = -88 from rfl] at hL
  have hL' := Abs.add_rbp (k := -8) hL (by
    simp [leave, h0])
  refine .inl (blkSt_entry (by decide) he hn ?_ ⟨?_, ?_⟩ hL' c1)
  · show Int64.ofBitVec (σ0.slot 8) = _
    rw [h8]; simp
  · rw [leave_cellsAS_slot (by simp [Region.Off, Region.callee]) hj]; exact hv
  · rw [leave_cellsAS_slot (by simp [Region.Off, Region.callee]) hj']; exact hv'

/-- **After `print`'s return the states stop at the `exit_group` call**:
`RetDt` is closed under certification, given `wc_main`'s `.x15` block and
`scc_rt_main`'s `exit_group` tail at their labels (`hc15`, `hcx`, `hcs`)
and the pieces off the transfer sites (`hns`). -/
theorem retDt_closed (hR : R0.OK) (hlo : R0.lo ≤ -224) (hhi : 0 ≤ R0.hi)
    (hc15 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label ".Lwc_main.x15") wcR15)
    (hcx : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label ".Lscc_rt_main.x3") (Flow.xExit (-48) 4 4 5))
    (hcs : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pcX exe) [(op64 .syscall, 2)])
    (hns : ∀ s, RetDt exe endPc R0 s → Kernel.siteAt abi μ s = none) :
    ClosedC A (Kernel.certSem abi A μ x tid) tid (RetDt exe endPc R0) := by
  have hW := wR_ok hR hlo hhi
  have hX : ClosedC A (Kernel.certSem abi A μ x tid) tid (ExitSt exe endPc (pcX exe)) :=
    exitSt_closed hcs fun s h => hns s (.inr (.inr h))
  have hM := ClosedC.rel (blkSt_steps (Tgt := ExitSt exe endPc (pcX exe)) hcx
    (Flow.xExit_ok (lo := -72) (hi := 0) (-48) 4 4 5 (by decide)) hR (by omega) hhi (fun _ _ _ _ => trivial)
    (fun s h => hns s (.inr (.inl h))) (fun σ0 _ s m he hn hA _ => ?_)) hX
  · refine ClosedC.rel (blkSt_steps (Tgt := fun s => _ ∨ _) hc15 wcR15_ok hW (Int.le_refl _) (Int.le_refl _)
      (callerCells_stable hR (by omega) (by decide) (by omega) (by decide) (by decide) (by decide))
      (fun s h => hns s (.inl h)) (fun σ0 hJ s m he hn hA hC => ?_)) hM
    obtain ⟨hra, hfp⟩ := hJ
    rw [wcR15_run] at hA ⊢
    have hL := abs_leave_cells hA hC
    rw [show (-80 : Int) + 8 = -72 from rfl] at hL
    have hL' := Abs.add_rbp (k := -8) hL (by
      simp [leave, hfp])
    exact .inl (blkSt_entry (by decide) he hn hra trivial hL' trivial)
  · obtain ⟨hpc, hrax, -⟩ := Flow.xExit_run (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label ".Lscc_rt_main.x3") (-72) (-8) σ0 (-48) 4 4 5
    refine ⟨he, hn, hpc, ?_⟩
    show m.regs.get64 .rax = 231
    rw [hA.regs]
    simp only [Reg64s.get64]
    exact BitVec.eq_of_toNat_eq (by simpa using hrax)

end Steps

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.X64.Rt.cp_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cp_stable

/--
info: 'Spike.Lib.X64.Rt.retDt_of_ret' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms retDt_of_ret

/--
info: 'Spike.Lib.X64.Rt.retDt_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms retDt_closed

end Spike.Lib.X64.Rt
