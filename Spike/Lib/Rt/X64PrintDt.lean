/-
**`scc_rt_print`'s write tail inside its frame** (x86-64): from the
routine's `write` system call on, its states (`Spike/Lib/X64Print.lean`'s
blocks, in the routine's region `Rp`, the caller's `%rbp` and the return
address in their cells, under a frame condition `C` no write inside `Rp`
breaks) step among themselves or out of the frame, at the return (`x13`'s
`ret`) or the abort call (`x12`'s `call scc_rt_abort`), keeping the promise
set. The pieces (`Spike/Lib/Rt/X64TailDt.lean`): one `BlkSt` per block of
the loop (`x2` … `x11`) and of the exits (`x12`, `x13`), and a `SysSt` at
the `write` call.

- `PJ rbp0 ra`: the frame's facts the pieces keep: the caller's `%rbp` at
  `0`, the return address at `8`;
- `PrintIn exe endPc Rp rbp0 ra C`: the union of the pieces;
- `printIn_steps`: a certification step from `PrintIn` lands in `PrintIn`
  or in `Out`, given the routine's code, the pieces off the transfer sites
  (`hns`) and the exits' landings in `Out` (`hret`, `hfail`, for every
  machine data related to the exit blocks' runs);
- `printIn_of_at`: the `write` node (`At … (Print.N … .sys)`) is in
  `PrintIn`.
-/
import Spike.Lib.Rt.X64TailDt
import Spike.Lib.X64Print

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem
open Scc.Sem.X64 (abi)
open Spike.Lib.X64
open Spike.Lib (ClosedC StepsTo upd upd_apply)
open Spike.Lib.X64.Print (x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 oI)

/-! ## The pieces -/

/-- **The frame's facts**: the caller's `%rbp` at `0`, the return address at
`8`. -/
def PJ (rbp0 ra : BitVec 64) (σ : AS) : Prop := σ.slot 0 = rbp0 ∧ σ.slot 8 = ra

section Pieces

variable (exe : _root_.Executable) (endPc : Int64) (Rp : Region) (rbp0 ra : BitVec 64) (C : MachineData → Prop)

/-- **At the `write` call**: `%rdi = 1`, `%rax = 1` (`Print.N … .sys`'s
facts), the machine data related to the frame's abstract state, and `C`. -/
def PSys (s : State) : Prop :=
  ∃ σ, PJ rbp0 ra σ ∧ σ.regs.get64 .rdi = 1 ∧ σ.regs.get64 .rax = 1 ∧ Abs Rp oI s.st.1 σ ∧ C s.st.1

/-- **`scc_rt_print`'s write tail inside its frame**: one of its pieces. -/
abbrev PrintIn (s : State) : Prop :=
  BlkSt exe endPc Rp ((_root_.Executable.labels exe).label ".Lscc_rt_print.loop") oI x2 (PJ rbp0 ra) C s ∨
  BlkSt exe endPc Rp ((_root_.Executable.labels exe).label ".Lscc_rt_print.loop" + 20) oI x3 (PJ rbp0 ra) C s ∨
  BlkSt exe endPc Rp ((_root_.Executable.labels exe).label ".Lscc_rt_print.write") oI x4 (PJ rbp0 ra) C s ∨
  SysSt exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_print.write" + 20) (PSys Rp rbp0 ra C) s ∨
  BlkSt exe endPc Rp ((_root_.Executable.labels exe).label ".Lscc_rt_print.write" + 22) oI x5 (PJ rbp0 ra) C s ∨
  BlkSt exe endPc Rp ((_root_.Executable.labels exe).label ".Lscc_rt_print.write" + 42) oI x6 (PJ rbp0 ra) C s ∨
  BlkSt exe endPc Rp ((_root_.Executable.labels exe).label ".Lscc_rt_print.chk2") oI x7 (PJ rbp0 ra) C s ∨
  BlkSt exe endPc Rp ((_root_.Executable.labels exe).label ".Lscc_rt_print.chk2" + 16) oI x8 (PJ rbp0 ra) C s ∨
  BlkSt exe endPc Rp ((_root_.Executable.labels exe).label ".Lscc_rt_print.chk3") oI x9 (PJ rbp0 ra) C s ∨
  BlkSt exe endPc Rp ((_root_.Executable.labels exe).label ".Lscc_rt_print.chk3" + 16) oI x10 (PJ rbp0 ra) C s ∨
  BlkSt exe endPc Rp ((_root_.Executable.labels exe).label ".Lscc_rt_print.adv") oI x11 (PJ rbp0 ra) C s ∨
  BlkSt exe endPc Rp ((_root_.Executable.labels exe).label ".Lscc_rt_print.fail") oI x12 (PJ rbp0 ra) C s ∨
  BlkSt exe endPc Rp ((_root_.Executable.labels exe).label ".Lscc_rt_print.done") oI x13 (PJ rbp0 ra) C s

end Pieces

/-! ## The steps -/

section Steps

variable {A : Arch} {μ : Marks} {x : Kernel.KState} {tid : Nat}
  {exe : _root_.Executable} {endPc : Int64} {Rp : Region} {rbp0 ra : BitVec 64} {C : MachineData → Prop}

/-- The tail. -/
local notation "PI" => PrintIn exe endPc Rp rbp0 ra C

/-- A step into the union: the piece `D` steps into `T`, `D` and `T` inside
`G ∨ O`. -/
private theorem into {D T G O : State → Prop} (h : StepsTo A (Kernel.certSem abi A μ x tid) tid D T)
    (hD : ∀ s, D s → G s) (hT : ∀ s, T s → G s ∨ O s) :
    ∀ p q : Thread isa × Memory, D p.1.st → ThreadStepC A (Kernel.certSem abi A μ x tid) tid p q →
      (G q.1.st ∨ O q.1.st) ∧ q.1.prom = p.1.prom := by
  intro p q hd hs
  obtain ⟨h1, h2⟩ := h p q hd hs
  exact ⟨h1.elim (fun h => .inl (hD _ h)) (hT _), h2⟩

/-- The frame's facts survive a write below `0`. -/
private theorem pj_upd {σ : AS} {k : Int} {v : BitVec 64} (h : PJ rbp0 ra σ) (hk : k < 0) :
    PJ rbp0 ra { σ with slot := upd σ.slot k v } := by
  obtain ⟨h0, h8⟩ := h
  refine ⟨?_, ?_⟩
  · show upd σ.slot k v 0 = rbp0
    have : (0 : Int) ≠ k := by omega
    simp [upd_apply, this, h0]
  · show upd σ.slot k v 8 = ra
    have : (8 : Int) ≠ k := by omega
    simp [upd_apply, this, h8]

/-- **A step from `scc_rt_print`'s write tail** lands in it or in `Out`,
keeping the promises, given the routine's code (`hcode`, any ghosts), the
region's facts, `C` kept by writes inside the region (`hC`), the pieces
off the transfer sites (`hns`), and the exit blocks' runs landing in `Out`:
the return (`hret`, `x13`) and the abort call (`hfail`, `x12`). -/
theorem printIn_steps {Out : State → Prop} {c0 : Ctl} {rbp0' ra' : BitVec 64}
    (hcode : Print.Code c0 rbp0' ra' exe endPc) (hR : Rp.OK) (hlo : Rp.lo ≤ -40) (hhi : 16 ≤ Rp.hi)
    (hC : FStable Rp C) (hns : ∀ s, PrintIn exe endPc Rp rbp0 ra C s → Kernel.siteAt abi μ s = none)
    (hret : ∀ σ0, PJ rbp0 ra σ0 → ∀ (s : State) m, s.exe = exe → s.endPc = endPc →
      Abs Rp (arun (_root_.Executable.labels exe).label x13
        ⟨(_root_.Executable.labels exe).label ".Lscc_rt_print.done", oI, σ0⟩).so m
        (arun (_root_.Executable.labels exe).label x13
          ⟨(_root_.Executable.labels exe).label ".Lscc_rt_print.done", oI, σ0⟩).σ → C m →
      Out { s with st := (m, (arun (_root_.Executable.labels exe).label x13
        ⟨(_root_.Executable.labels exe).label ".Lscc_rt_print.done", oI, σ0⟩).pc) })
    (hfail : ∀ σ0, PJ rbp0 ra σ0 → ∀ (s : State) m, s.exe = exe → s.endPc = endPc →
      Abs Rp (arun (_root_.Executable.labels exe).label x12
        ⟨(_root_.Executable.labels exe).label ".Lscc_rt_print.fail", oI, σ0⟩).so m
        (arun (_root_.Executable.labels exe).label x12
          ⟨(_root_.Executable.labels exe).label ".Lscc_rt_print.fail", oI, σ0⟩).σ → C m →
      Out { s with st := (m, (arun (_root_.Executable.labels exe).label x12
        ⟨(_root_.Executable.labels exe).label ".Lscc_rt_print.fail", oI, σ0⟩).pc) }) :
    StepsTo A (Kernel.certSem abi A μ x tid) tid (PrintIn exe endPc Rp rbp0 ra C) Out := by
  -- a block's entry, from the run's exit
  have ent : ∀ {pc : Int64} {blk : List (Directive × Nat)} (s : State) (m : MachineData) (σ : AS),
      0 < blk.length → s.exe = exe → s.endPc = endPc → Abs Rp oI m σ → PJ rbp0 ra σ → C m →
      BlkSt exe endPc Rp pc oI blk (PJ rbp0 ra) C { s with st := (m, pc) } :=
    fun s m σ hne he hn hA hJ hCm => blkSt_entry hne he hn rfl hJ hA hCm
  have hsite : ∀ {D : State → Prop}, (∀ s, D s → PrintIn exe endPc Rp rbp0 ra C s) →
      ∀ s, D s → Kernel.siteAt abi μ s = none := fun hD s h => hns s (hD s h)
  rintro p q hD hs
  rcases hD with h | h | h | h | h | h | h | h | h | h | h | h | h
  · -- `x2`: to `.done` or to `x3`
    refine into (blkSt_steps (Tgt := fun s => PI s ∨ Out s) hcode.loop Print.x2_ok hR hlo hhi hC
      (hsite fun _ h => .inl h) fun σ0 hJ s m he hn hA hCm => ?_) (fun _ h => .inl h) (fun _ h => h) p q h hs
    rw [Print.x2_run] at hA ⊢
    split
    · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (ent s m _ (by decide) he hn hA hJ hCm)))))))))))))
    · exact .inl (.inr (.inl (ent s m _ (by decide) he hn hA hJ hCm)))
  · -- `x3`: to `.write`
    refine into (blkSt_steps (Tgt := fun s => PI s ∨ Out s) hcode.n3 Print.x3_ok hR hlo hhi hC
      (hsite fun _ h => .inr (.inl h)) fun σ0 hJ s m he hn hA hCm => ?_) (fun _ h => .inr (.inl h))
      (fun _ h => h) p q h hs
    rw [Print.x3_run] at hA ⊢
    exact .inl (.inr (.inr (.inl (ent s m _ (by decide) he hn hA hJ hCm))))
  · -- `x4`: to the `write` call
    refine into (blkSt_steps (Tgt := fun s => PI s ∨ Out s) hcode.write Print.x4_ok hR hlo hhi hC
      (hsite fun _ h => .inr (.inr (.inl h))) fun σ0 hJ s m he hn hA hCm => ?_) (fun _ h => .inr (.inr (.inl h)))
      (fun _ h => h) p q h hs
    rw [Print.x4_run] at hA ⊢
    refine .inl (.inr (.inr (.inr (.inl ⟨he, hn, rfl, _, ?_, ?_, ?_, hA, hCm⟩))))
    · exact hJ
    · simp
    · simp
  · -- the `write` call: to `x5`
    refine into (sysSt_steps (Tgt := fun s => PI s ∨ Out s)
      (call := fun s => .write 1 (s.st.1.regs.get64 .rsi).toNat (s.st.1.regs.get64 .rdx).toNat) hcode.sys
      (hsite fun _ h => .inr (.inr (.inr (.inl h)))) ?_ ?_ ?_ ?_) (fun _ h => .inr (.inr (.inr (.inl h))))
      (fun _ h => h) p q h hs
    · rintro s ⟨σ, -, h1, ha, hA, -⟩
      rw [← hA.regs] at h1 ha
      simp only [Reg64s.get64] at h1 ha
      have ha' : s.st.1.regs.rax.toNat = 1 := by rw [← UInt64.toNat_toBitVec, ha]; rfl
      have h1' : s.st.1.regs.rdi.toNat = 1 := by rw [← UInt64.toNat_toBitVec, h1]; rfl
      simp [syscallCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64, ha', h1', Reg64s.get64]
    · intro _ _ _ h; cases h
    · intro _ _ _ _ h; cases h
    · rintro s he hn - ⟨σ, hJ, -, -, hA, hCm⟩ v -
      refine .inl (.inr (.inr (.inr (.inr (.inl ?_)))))
      have hpc : (Print.N (_root_.Executable.labels exe).label c0 rbp0' ra' .sys).pc + Int64.ofNat 2 =
          (_root_.Executable.labels exe).label ".Lscc_rt_print.write" + 22 := by
        show (_root_.Executable.labels exe).label ".Lscc_rt_print.write" + 20 + Int64.ofNat 2 = _
        rw [Int64.add_assoc]; rfl
      rw [hpc]
      exact ent s _ (syscallStep _ v σ) (by decide) he hn (Abs.syscallRet hA _ v) hJ
        (hC _ _ hCm fun _ _ _ => rfl)
  · -- `x5`: to `.loop` or to `x6`
    refine into (blkSt_steps (Tgt := fun s => PI s ∨ Out s) hcode.n5 Print.x5_ok hR hlo hhi hC
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inl h))))) fun σ0 hJ s m he hn hA hCm => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inl h))))) (fun _ h => h) p q h hs
    rw [Print.x5_run] at hA ⊢
    have hJ' := pj_upd (k := -24) (v := σ0.regs.rax.toBitVec) hJ (by decide)
    split
    · exact .inl (.inl (ent s m _ (by decide) he hn hA hJ' hCm))
    · refine .inl (.inr (.inr (.inr (.inr (.inr (.inl ?_))))))
      have hpc : (Print.N (_root_.Executable.labels exe).label c0 rbp0' ra' .n5).pc + 20 =
          (_root_.Executable.labels exe).label ".Lscc_rt_print.write" + 42 := by
        show (_root_.Executable.labels exe).label ".Lscc_rt_print.write" + 22 + 20 = _
        rw [Int64.add_assoc]; rfl
      rw [hpc]
      exact ent s m _ (by decide) he hn hA hJ' hCm
  · -- `x6`: to `.chk2`
    refine into (blkSt_steps (Tgt := fun s => PI s ∨ Out s) hcode.n6 Print.x6_ok hR hlo hhi hC
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inl h)))))) fun σ0 hJ s m he hn hA hCm => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inl h)))))) (fun _ h => h) p q h hs
    rw [Print.x6_run] at hA ⊢
    exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inl (ent s m _ (by decide) he hn hA hJ hCm))))))))
  · -- `x7`: to `.loop` or to `x8`
    refine into (blkSt_steps (Tgt := fun s => PI s ∨ Out s) hcode.chk2 Print.x7_ok hR hlo hhi hC
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))) fun σ0 hJ s m he hn hA hCm => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))) (fun _ h => h) p q h hs
    rw [Print.x7_run] at hA ⊢
    split
    · exact .inl (.inl (ent s m _ (by decide) he hn hA hJ hCm))
    · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (ent s m _ (by decide) he hn hA hJ hCm)))))))))
  · -- `x8`: to `.chk3`
    refine into (blkSt_steps (Tgt := fun s => PI s ∨ Out s) hcode.n8 Print.x8_ok hR hlo hhi hC
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))) fun σ0 hJ s m he hn hA hCm => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))) (fun _ h => h) p q h hs
    rw [Print.x8_run] at hA ⊢
    exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      (ent s m _ (by decide) he hn hA hJ hCm))))))))))
  · -- `x9`: to `.fail` or to `x10`
    refine into (blkSt_steps (Tgt := fun s => PI s ∨ Out s) hcode.chk3 Print.x9_ok hR hlo hhi hC
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))
      fun σ0 hJ s m he hn hA hCm => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))) (fun _ h => h) p q h hs
    rw [Print.x9_run] at hA ⊢
    split
    · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
        (ent s m _ (by decide) he hn hA hJ hCm)))))))))))))
    · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
        (ent s m _ (by decide) he hn hA hJ hCm)))))))))))
  · -- `x10`: to `.adv`
    refine into (blkSt_steps (Tgt := fun s => PI s ∨ Out s) hcode.n10 Print.x10_ok hR hlo hhi hC
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))))
      fun σ0 hJ s m he hn hA hCm => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))) (fun _ h => h) p q h hs
    rw [Print.x10_run] at hA ⊢
    exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      (ent s m _ (by decide) he hn hA hJ hCm))))))))))))
  · -- `x11`: to `.loop`
    refine into (blkSt_steps (Tgt := fun s => PI s ∨ Out s) hcode.adv Print.x11_ok hR hlo hhi hC
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))))
      fun σ0 hJ s m he hn hA hCm => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))))
      (fun _ h => h) p q h hs
    rw [Print.x11_run] at hA ⊢
    obtain ⟨h0, h8⟩ := hJ
    exact .inl (.inl (ent s m _ (by decide) he hn hA ⟨by simp [upd_apply, h0], by simp [upd_apply, h8]⟩ hCm))
  · -- `x12`: the abort call
    refine into (blkSt_steps (Tgt := fun s => PI s ∨ Out s) hcode.fail Print.x12_ok hR hlo hhi hC
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))))))
      fun σ0 hJ s m he hn hA hCm => .inr (hfail σ0 hJ s m he hn hA hCm))
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))))))
      (fun _ h => h) p q h hs
  · -- `x13`: the return
    refine into (blkSt_steps (Tgt := fun s => PI s ∨ Out s) hcode.done Print.x13_ok hR hlo hhi hC
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))))))))
      fun σ0 hJ s m he hn hA hCm => .inr (hret σ0 hJ s m he hn hA hCm))
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))))))))
      (fun _ h => h) p q h hs

end Steps

/-! ## Entry -/

/-- **The `write` node is in the tail**: at `Print.N … .sys`, under a frame
condition `F`. -/
theorem printIn_of_at {exe : _root_.Executable} {endPc : Int64} {Rp : Region} {F : MachineData → Prop}
    {c0 c : Ctl} {rbp0 ra : BitVec 64} {s : State}
    (hAt : At exe endPc Rp F (Print.N (_root_.Executable.labels exe).label c0 rbp0 ra .sys) s c) :
    PrintIn exe endPc Rp rbp0 ra F s := by
  obtain ⟨he, hn, -, hpc, σ, hA, hD, ⟨-, h0, h8⟩, h1, h2⟩ := hAt
  exact .inr (.inr (.inr (.inl ⟨he, hn, hpc, σ, ⟨h0, h8⟩, h1, h2, hA, hD⟩)))

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.X64.Rt.printIn_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms printIn_steps

/--
info: 'Spike.Lib.X64.Rt.printIn_of_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms printIn_of_at

end Spike.Lib.X64.Rt
