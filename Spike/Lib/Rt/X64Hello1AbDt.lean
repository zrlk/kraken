/-
**`hello1.w`'s write tail on `print`'s abort** (x86-64): from `print`'s
`call scc_rt_abort` (`Print.x12`, `%rdi = 4`), the dispatcher's blocks up to
its jump to `scc_rt_abort_write` (`Abort.Disp`: the prologue storing the
code, the failed tests against 1, 2, 3 and their jumps, the test against 4
and the jump out), then the `write` stub's prologue, its `leaq` of the
message and its argument block, up to its `write` call, where the stub's
tail `StubDt` (`Spike/Lib/Rt/X64StubDt.lean`) takes over. The pieces are
`Spike/Lib/Rt/X64TailDt.lean`'s, in one region `RA` serving the dispatcher
and the stub (the stub reuses the dispatcher's frame base), with no frame
condition: the path does not return.

- `SiSt`, `siSt_steps`: at a single `SI` (no event), the piece steps past it;
- `stubDt_of_abs`: a stub's `write` call with the machine data related at
  `Abort.oI` in a region holding the stub's frame is in `StubDt`;
- `AbIn exe endPc RA`: the eleven pieces; `abIn_steps`: a step from
  `AbIn` lands in `AbIn` or in the `write` stub's `StubDt`, given the
  dispatcher's and the stub's code and the pieces off the transfer sites;
- `abIn_of_fail`: `print`'s abort call lands in `AbIn` (the `hfail` of
  `printIn_steps` in `hello1.w`'s regions: `scc_rt_abort`'s region at
  `R0.callee (-232) (-24) 16`, below `wc_main`'s).
-/
import Spike.Lib.Rt.X64Hello1RetDt
import Spike.Lib.Rt.X64StubDt
import Spike.Lib.X64Abort

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem
open Scc.Sem.X64 (abi)
open Spike.Lib.X64
open Spike.Lib (ClosedC StepsTo upd upd_apply)
open Spike.Lib.LowerX64 (spill Spilled)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Flow.Hello1 (wR pR)

/-! ## A single `SI` -/

/-- **At a single `SI`** `si` at `pc` (static offsets `o`, region `R`): the
machine data related to an abstract state of `J`, and `C`. -/
def SiSt (exe : _root_.Executable) (endPc : Int64) (R : Region) (pc : Int64) (o : SO) (J : AS → Prop)
    (C : MachineData → Prop) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧ s.st.2 = pc ∧ ∃ σ, J σ ∧ Abs R o s.st.1 σ ∧ C s.st.1

section Si

variable {A : Arch} {μ : Marks} {x : Kernel.KState} {tid : Nat}

/-- **A step at a single `SI`** goes past it: in `Tgt` for every machine
data related to the `SI`'s step and in `C` (`hland`), given its code, its
`ok`, `C` kept by register writes (`hC`) and the piece off the transfer
sites (`hns`). -/
theorem siSt_steps {exe : _root_.Executable} {endPc : Int64} {R : Region} {pc : Int64} {o : SO} {si : SI}
    {z : Nat} {J : AS → Prop} {C : MachineData → Prop} {Tgt : State → Prop}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc [(si.toDir, z)]) (hok : si.ok = true)
    (hC : FStable R C) (hns : ∀ s, SiSt exe endPc R pc o J C s → Kernel.siteAt abi μ s = none)
    (hland : ∀ σ, J σ → ∀ (s : State) m, s.exe = exe → s.endPc = endPc →
      Abs R (si.so o) m (si.step (_root_.Executable.labels exe).label σ) → C m →
      Tgt { s with st := (m, pc + Int64.ofNat z) }) :
    StepsTo A (Kernel.certSem abi A μ x tid) tid (SiSt exe endPc R pc o J C) Tgt := by
  refine StepsTo.of_into fun ⟨t, mem⟩ q hD h => ?_
  have hsi := hns _ hD
  obtain ⟨he, hn, hpc, σ, hJ, hA, hCm⟩ := hD
  have hc : CellAt t.st si.toDir z := (hcode t.st he hn).cell0 rfl rfl hpc
  have hl : labelAddr t.st = (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels t.st.exe).label L = _; rw [he]
  obtain ⟨hpr, hq⟩ := si_stepC hsi hc h
  refine ⟨?_, hpr⟩
  rw [hq, hl]
  have := hland σ hJ t.st _ he hn (SI.abs _ hok hA) (hC _ _ hCm fun _ _ _ => rfl)
  simp only [after]
  rw [show t.st.st.2 = pc from hpc]
  exact this

end Si

/-- **A stub's `write` call is in its tail**, the machine data related at
`Abort.oI` in a region holding the stub's frame `[-24, 16)`, `%rax = 1`,
`%rdi = 2`. -/
theorem stubDt_of_abs {exe : _root_.Executable} {endPc : Int64} {st : Abort.Stub} {R : Region} {s : State}
    {σ : AS} (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (he : s.exe = exe) (hn : s.endPc = endPc)
    (hpc : s.st.2 = Abort.pcSys (_root_.Executable.labels exe).label st) (hA : Abs R Abort.oI s.st.1 σ)
    (hax : σ.regs.get64 .rax = 1) (hdi : σ.regs.get64 .rdi = 2) :
    StubDt exe endPc (_root_.Executable.labels exe).label st s := by
  have hbp : s.st.1.regs.get64 .rbp = R.addr 0 := by rw [hA.regs]; exact hA.so .rbp 0 rfl
  obtain ⟨j, hj, -⟩ := hA.slot (-16) ⟨by decide, by omega, by omega⟩
  refine ⟨he, hn, .inl ⟨hpc, by rw [hA.regs]; exact hax, by rw [hA.regs]; exact hdi, j, ?_⟩⟩
  unfold spill slotA
  rw [hbp, BitVec.ofInt_add, BitVec.ofInt_toInt, ← Region.addr_add,
    show (0 : Int) + (-16 : Int64).toInt = -16 by decide]
  exact hj

/-! ## The pieces -/

section Pieces

variable (exe : _root_.Executable) (endPc : Int64) (RA : Region)

/-- The stored code is `4`. -/
def J4 (σ : AS) : Prop := σ.slot (-8) = 4#64

/-- **`print`'s abort path up to the `write` stub's `write` call**: the
dispatcher's blocks on code `4`, the stub's prologue, its `leaq` and its
argument block, in `scc_rt_abort`'s region `RA`. -/
def AbIn (s : State) : Prop :=
  BlkSt exe endPc RA ((_root_.Executable.labels exe).label "scc_rt_abort") Abort.oE Abort.Disp.d0
    (fun σ => σ.regs.get64 .rdi = 4) (fun _ => True) s ∨
  BlkSt exe endPc RA ((_root_.Executable.labels exe).label ".Lscc_rt_abort.entry") Abort.Disp.oD Abort.Disp.t1
    J4 (fun _ => True) s ∨
  BlkSt exe endPc RA ((_root_.Executable.labels exe).label ".Lscc_rt_abort.entry" + 16) Abort.Disp.oD
    Abort.Disp.j1 J4 (fun _ => True) s ∨
  BlkSt exe endPc RA ((_root_.Executable.labels exe).label ".Lscc_rt_abort.next1") Abort.Disp.oD Abort.Disp.t2
    J4 (fun _ => True) s ∨
  BlkSt exe endPc RA ((_root_.Executable.labels exe).label ".Lscc_rt_abort.next1" + 16) Abort.Disp.oD
    Abort.Disp.j2 J4 (fun _ => True) s ∨
  BlkSt exe endPc RA ((_root_.Executable.labels exe).label ".Lscc_rt_abort.next3") Abort.Disp.oD Abort.Disp.t3
    J4 (fun _ => True) s ∨
  BlkSt exe endPc RA ((_root_.Executable.labels exe).label ".Lscc_rt_abort.next3" + 16) Abort.Disp.oD
    Abort.Disp.j3 J4 (fun _ => True) s ∨
  BlkSt exe endPc RA ((_root_.Executable.labels exe).label ".Lscc_rt_abort.next5") Abort.Disp.oD Abort.Disp.t4
    J4 (fun _ => True) s ∨
  BlkSt exe endPc RA ((_root_.Executable.labels exe).label ".Lscc_rt_abort.is6") Abort.Disp.oD Abort.Disp.g4
    (fun _ => True) (fun _ => True) s ∨
  BlkSt exe endPc RA ((_root_.Executable.labels exe).label Abort.write.fn) Abort.oE Abort.x0
    (fun _ => True) (fun _ => True) s ∨
  SiSt exe endPc RA ((_root_.Executable.labels exe).label Abort.write.entry) Abort.oI (fun _ => True)
    (fun _ => True) s ∨
  BlkSt exe endPc RA ((_root_.Executable.labels exe).label Abort.write.entry + 7) Abort.oI Abort.x1Write
    (fun _ => True) (fun _ => True) s

end Pieces

section Steps

variable {A : Arch} {μ : Marks} {x : Kernel.KState} {tid : Nat}
  {exe : _root_.Executable} {endPc : Int64} {RA : Region}

/-- The pieces. -/
local notation "AI" => AbIn exe endPc RA

/-- A step into the union: the piece `D` steps into `T`, `D` and `T` inside
`G ∨ O`. -/
private theorem into {D T G O : State → Prop} (h : StepsTo A (Kernel.certSem abi A μ x tid) tid D T)
    (hD : ∀ s, D s → G s) (hT : ∀ s, T s → G s ∨ O s) :
    ∀ p q : Thread isa × Memory, D p.1.st → ThreadStepC A (Kernel.certSem abi A μ x tid) tid p q →
      (G q.1.st ∨ O q.1.st) ∧ q.1.prom = p.1.prom := by
  intro p q hd hs
  obtain ⟨h1, h2⟩ := h p q hd hs
  exact ⟨h1.elim (fun h => .inl (hD _ h)) (hT _), h2⟩

/-- **A step from `print`'s abort path** lands in it or in the `write`
stub's tail, given the dispatcher's code (`hd`), the stub's (`hs`), the
region's facts and the pieces off the transfer sites (`hns`). -/
theorem abIn_steps {c0 c1 : Ctl} (hd : Abort.Disp.Code c0 exe endPc) (hs : Abort.Code Abort.write c1
      Abort.x1Write exe endPc) (hR : RA.OK) (hlo : RA.lo ≤ -24) (hhi : 16 ≤ RA.hi)
    (hns : ∀ s, AI s → Kernel.siteAt abi μ s = none) :
    StepsTo A (Kernel.certSem abi A μ x tid) tid AI
      (StubDt exe endPc (_root_.Executable.labels exe).label Abort.write) := by
  have ent : ∀ {pc : Int64} {o : SO} {blk : List (Directive × Nat)} {J : AS → Prop} (s : State)
      (m : MachineData) (σ : AS), 0 < blk.length → s.exe = exe → s.endPc = endPc → Abs RA o m σ → J σ →
      BlkSt exe endPc RA pc o blk J (fun _ => True) { s with st := (m, pc) } :=
    fun s m σ hne he hn hA hJ => blkSt_entry hne he hn rfl hJ hA trivial
  have hsite : ∀ {D : State → Prop}, (∀ s, D s → AI s) → ∀ s, D s → Kernel.siteAt abi μ s = none :=
    fun hD s h => hns s (hD s h)
  have hT : FStable RA (fun _ => True) := fun _ _ _ _ => trivial
  have hlo8 : RA.lo ≤ -8 := by omega
  rintro p q hD hst
  rcases hD with h | h | h | h | h | h | h | h | h | h | h | h
  · -- `d0`: the prologue storing the code, to `t1`
    refine into (blkSt_steps (Tgt := fun s => AI s ∨ _) hd.e Abort.Disp.d0_ok hR hlo8 hhi hT
      (hsite fun _ h => .inl h) fun σ0 hJ s m he hn hA _ => ?_) (fun _ h => .inl h) (fun _ h => h) p q h hst
    rw [Abort.Disp.d0_run] at hA ⊢
    rw [show (Abort.Disp.DN.nd (_root_.Executable.labels exe).label c0 .e).pc + 12 =
      (_root_.Executable.labels exe).label ".Lscc_rt_abort.entry" from hd.hentry.symm]
    refine .inl (.inr (.inl (ent s m _ (by decide) he hn hA ?_)))
    simp only [J4, upd_apply, ↓reduceIte]
    simpa [Reg64s.get64] using hJ
  · -- `t1`: fails, to `j1`
    refine into (blkSt_steps (Tgt := fun s => AI s ∨ _) hd.t1 Abort.Disp.t1_ok hR hlo8 hhi hT
      (hsite fun _ h => .inr (.inl h)) fun σ0 hJ s m he hn hA _ => ?_) (fun _ h => .inr (.inl h))
      (fun _ h => h) p q h hst
    rw [Abort.Disp.t1_run] at hA ⊢
    have hc : ¬ σ0.slot (-8) - 1#64 = 0#64 := by rw [hJ]; decide
    simp only [hc, ↓reduceIte] at hA ⊢
    exact .inl (.inr (.inr (.inl (ent s m _ (by decide) he hn hA hJ))))
  · -- `j1`: to `t2`
    refine into (blkSt_steps (Tgt := fun s => AI s ∨ _) hd.j1 Abort.Disp.j1_ok hR hlo8 hhi hT
      (hsite fun _ h => .inr (.inr (.inl h))) fun σ0 hJ s m he hn hA _ => ?_) (fun _ h => .inr (.inr (.inl h)))
      (fun _ h => h) p q h hst
    rw [Abort.Disp.j1_run] at hA ⊢
    exact .inl (.inr (.inr (.inr (.inl (ent s m _ (by decide) he hn hA hJ)))))
  · -- `t2`: fails, to `j2`
    refine into (blkSt_steps (Tgt := fun s => AI s ∨ _) hd.t2 Abort.Disp.t2_ok hR hlo8 hhi hT
      (hsite fun _ h => .inr (.inr (.inr (.inl h)))) fun σ0 hJ s m he hn hA _ => ?_)
      (fun _ h => .inr (.inr (.inr (.inl h)))) (fun _ h => h) p q h hst
    rw [Abort.Disp.t2_run] at hA ⊢
    have hc : ¬ σ0.slot (-8) - 2#64 = 0#64 := by rw [hJ]; decide
    simp only [hc, ↓reduceIte] at hA ⊢
    exact .inl (.inr (.inr (.inr (.inr (.inl (ent s m _ (by decide) he hn hA hJ))))))
  · -- `j2`: to `t3`
    refine into (blkSt_steps (Tgt := fun s => AI s ∨ _) hd.j2 Abort.Disp.j2_ok hR hlo8 hhi hT
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inl h))))) fun σ0 hJ s m he hn hA _ => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inl h))))) (fun _ h => h) p q h hst
    rw [Abort.Disp.j2_run] at hA ⊢
    exact .inl (.inr (.inr (.inr (.inr (.inr (.inl (ent s m _ (by decide) he hn hA hJ)))))))
  · -- `t3`: fails, to `j3`
    refine into (blkSt_steps (Tgt := fun s => AI s ∨ _) hd.t3 Abort.Disp.t3_ok hR hlo8 hhi hT
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inl h)))))) fun σ0 hJ s m he hn hA _ => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inl h)))))) (fun _ h => h) p q h hst
    rw [Abort.Disp.t3_run] at hA ⊢
    have hc : ¬ σ0.slot (-8) - 3#64 = 0#64 := by rw [hJ]; decide
    simp only [hc, ↓reduceIte] at hA ⊢
    exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inl (ent s m _ (by decide) he hn hA hJ))))))))
  · -- `j3`: to `t4`
    refine into (blkSt_steps (Tgt := fun s => AI s ∨ _) hd.j3 Abort.Disp.j3_ok hR hlo8 hhi hT
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))) fun σ0 hJ s m he hn hA _ => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))) (fun _ h => h) p q h hst
    rw [Abort.Disp.j3_run] at hA ⊢
    exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (ent s m _ (by decide) he hn hA hJ)))))))))
  · -- `t4`: matches, to `g4`
    refine into (blkSt_steps (Tgt := fun s => AI s ∨ _) hd.t4 Abort.Disp.t4_ok hR hlo8 hhi hT
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))) fun σ0 hJ s m he hn hA _ => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))) (fun _ h => h) p q h hst
    rw [Abort.Disp.t4_run] at hA ⊢
    have hc : σ0.slot (-8) - 4#64 = 0#64 := by rw [hJ]; decide
    simp only [hc, ↓reduceIte] at hA ⊢
    exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      (ent s m _ (by decide) he hn hA trivial))))))))))
  · -- `g4`: the jump to the stub
    refine into (blkSt_steps (Tgt := fun s => AI s ∨ _) hd.g4 Abort.Disp.g4_ok hR hlo8 hhi hT
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))
      fun σ0 _ s m he hn hA _ => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))) (fun _ h => h) p q h hst
    rw [Abort.Disp.g4_run] at hA ⊢
    exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      (ent s m _ (by decide) he hn hA trivial)))))))))))
  · -- the stub's prologue, to the `leaq`
    refine into (blkSt_steps (Tgt := fun s => AI s ∨ _) hs.e Abort.x0_ok hR hlo hhi hT
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))))
      fun σ0 _ s m he hn hA _ => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))) (fun _ h => h) p q h hst
    rw [Abort.x0_run] at hA ⊢
    rw [show (Abort.N (_root_.Executable.labels exe).label Abort.write c1 .e).pc + 8 =
      (_root_.Executable.labels exe).label Abort.write.entry from hs.hentry.symm]
    exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨he, hn, rfl, _, trivial, hA, trivial⟩)))))))))))
  · -- the `leaq`, to the argument block
    refine into (siSt_steps (Tgt := fun s => AI s ∨ _) hs.n1 (by decide) hT
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))))
      fun σ0 _ s m he hn hA _ => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))))
      (fun _ h => h) p q h hst
    exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (ent s m _ (by decide) he hn hA trivial))))))))))))
  · -- the argument block, to the `write` call
    refine into (blkSt_steps (Tgt := fun s => AI s ∨ _) hs.n2 Abort.x1Write_ok hR hlo hhi hT
      (hsite fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h)))))))))))
      fun σ0 _ s m he hn hA _ => ?_)
      (fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h)))))))))))
      (fun _ h => h) p q h hst
    rw [Abort.x1Write_run] at hA ⊢
    refine .inr (stubDt_of_abs hlo hhi he hn ?_ hA (by simp) (by simp))
    show (_root_.Executable.labels exe).label Abort.write.entry + 7 + 27 = _
    rw [Int64.add_assoc]; rfl

end Steps

/-! ## Entry from `print`'s abort call -/

/-- **Machine data with every cell of a region holding a value** is related
at `⟨sp, []⟩` to its registers and the cells' values, `%rsp` at `sp`. -/
theorem abs_cells {R : Region} {sp : Int} {m : MachineData} {σ : AS} (hr : m.regs = σ.regs)
    (hz : m.zmms = σ.zmms) (hs : m.status = σ.status) (hsp : σ.regs.get64 .rsp = R.addr sp)
    (hc : ∀ k, R.Off k → (Mem.loadInt m.dmem (R.addr k) 8).isSome) : Abs R ⟨sp, []⟩ m (cellsAS R m σ) := by
  refine ⟨hr, hz, hs, fun r k h => ?_, fun k hk => ?_⟩
  · obtain ⟨rfl, rfl⟩ := SO.get_sp_only h; exact hsp
  · obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (hc k hk)
    exact ⟨j, hj, by simp only [cellsAS, hj]; rfl⟩

/-- `scc_rt_abort`'s region at `print`'s abort call in `hello1.w`: based at
the pushed return address (`-224` in `scc_rt_main`'s region `R0`), less
`Abort.oE`'s `8`. -/
abbrev aR (R0 : Region) : Region := R0.callee (-232) (-24) 16

/-- `scc_rt_abort`'s region is fine. -/
theorem aR_ok {R0 : Region} (hR : R0.OK) (hlo : R0.lo ≤ -256) (hhi : 0 ≤ R0.hi) : (aR R0).OK :=
  Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)

/-- **`print`'s abort call lands on the abort path**: `x12`'s run from
`print`'s frame under `print`'s frame condition is the dispatcher's entry in
`scc_rt_abort`'s region (the `hfail` of `printIn_steps`). -/
theorem abIn_of_fail {exe : _root_.Executable} {endPc : Int64} {R0 : Region} (hlo : R0.lo ≤ -256)
    (hhi : 0 ≤ R0.hi) (σ0 : AS) (s : State) (m : MachineData) (he : s.exe = exe) (hn : s.endPc = endPc)
    (hA : Abs (pR (wR R0)) (arun (_root_.Executable.labels exe).label Print.x12
        ⟨(_root_.Executable.labels exe).label ".Lscc_rt_print.fail", Print.oI, σ0⟩).so m
      (arun (_root_.Executable.labels exe).label Print.x12
        ⟨(_root_.Executable.labels exe).label ".Lscc_rt_print.fail", Print.oI, σ0⟩).σ)
    (hC : CP exe R0 m) :
    AbIn exe endPc (aR R0) { s with st := (m, (arun (_root_.Executable.labels exe).label Print.x12
      ⟨(_root_.Executable.labels exe).label ".Lscc_rt_print.fail", Print.oI, σ0⟩).pc) } := by
  obtain ⟨⟨c1, -⟩, -⟩ := hC
  rw [Print.x12_run] at hA ⊢
  have hsp := hA.so .rsp (-40) (SO.get_rsp _)
  have hA' := abs_cells (R := aR R0) (sp := 8) hA.regs hA.zmms hA.status (by
      rw [hsp]; simp only [Region.callee_addr]; exact congrArg R0.addr (by decide)) (fun k hk => ?_)
  · refine .inl (blkSt_entry (by decide) he hn rfl ?_ hA' trivial)
    simp [cellsAS]
  · obtain ⟨k8, klo, khi⟩ := hk
    simp only [Region.callee] at klo khi
    by_cases h8 : k = 8
    · subst h8
      obtain ⟨j, hj, -⟩ := hA.slot (-40) ⟨by decide, by simp [Region.callee], by simp [Region.callee]⟩
      have : (aR R0).addr 8 = (pR (wR R0)).addr (-40) := by
        simp only [Region.callee_addr]; exact congrArg R0.addr (by decide)
      rw [this, hj]; rfl
    · have := c1 (-232 + k) ⟨by omega, by omega, by omega⟩ (by simp only [Region.Off, Region.callee]; omega)
      rwa [Region.callee_addr]

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.X64.Rt.siSt_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms siSt_steps

/--
info: 'Spike.Lib.X64.Rt.stubDt_of_abs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stubDt_of_abs

/--
info: 'Spike.Lib.X64.Rt.abIn_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms abIn_steps

/--
info: 'Spike.Lib.X64.Rt.abIn_of_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms abIn_of_fail

end Spike.Lib.X64.Rt
