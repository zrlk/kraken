/-
**hello.w on x86-64: main after a refused `clone`, the slice's slots
carried** (the x86-64 twin of `Spike/Lib/A64HelloSpawnFailS.lean`):
`X64HelloSpawnFail`'s nodes with main's slots of all five of the spawn's
packet words. hello's spawn reads `p = sl ++ [c, me]`, so placing the source
on the refusal path needs the slice's words besides the cell at `-48` and
main's id at `-40`; `Hello.SpawnFail.MS` carries the latter two only. The
blocks store only to `-120` and the pushed return address at `-136`, so
every slot is kept.

- `MSS sl cA m`: main's slots `sl.1` at `-8`, `sl.2.2.1` at `-24`,
  `sl.2.2.2` at `-32` (the first, third and fourth arguments' slots), `cA`
  at `-48`, `m` at `-40`.
- `fNS lab cP sl cA m`, `fES lab cP sl cA m`: `SpawnFail.fN`/`fE` at `MSS`;
  the exit at `scc_rt_abort` with `%rdi = 5` and the return address
  `raT lab ".Lwc_main"` at `-136`.
- `seg_failWS`: from `fNS .ts` to `fES` inside `W`, in any cells passing
  `failIn`.
- `seg_spawnFailWS`: `seg_failWS` then `seg_jabort5W`, given the threads
  abort path's obligations (`StubTW`) per caller state.
- `seg_spawnFailWS_hello`: `seg_spawnFailWS` in any valid layout of
  `helloCells` (`hello_failIn`).

**Deviation from the A64 file.** The proofs are `X64WakeSpawnFail`'s
(`seg_failW`, `seg_spawnFailW`) at hello's frame of 128: the call pushes the
return address at `-136`, so `seg_failWS` needs `R.lo ≤ -136` and
`seg_spawnFailWS` `R.lo ≤ -168`, `16 ≤ R.hi` (no alignment premise); A64's
`-144`/`-192`, `0 ≤ R.hi`, `hal`. The slots are `%rbp` offsets (A64's `-144`,
`-128`, `-120`, `-104`, `-112`).
-/
import Spike.Lib.X64HelloSpawnFail

namespace Spike.Lib.X64.Flow.Worker.Hello.SpawnFail

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker.Hello.Child (x25L)
open Spike.Lib.X64.Flow.Worker.Hello.Parent (oP tsB jeB x26B x26L jeB_ok jeB_run x26B_ok x26B_run)
open Spike.Lib.X64.ThreadsAb (CloneRef raT)
open Scc.Cert.Rt.X64 (Lays endOf blockAt labelGap codeAt_blockAt_lays label_labelGap_lays)

/-! ## The nodes -/

/-- **Main's slots of the spawn's five packet words**: the slice's words
`sl.1` at `-8`, `sl.2.2.1` at `-24` and `sl.2.2.2` at `-32`, the box's cell
`cA` at `-48` and main's `ThreadId` word `m` at `-40` (hello's frame of
128). -/
def MSS (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (cA m : BitVec 64) (σ : AS) : Prop :=
  σ.slot (-8) = sl.1 ∧ σ.slot (-24) = sl.2.2.1 ∧ σ.slot (-32) = sl.2.2.2 ∧ σ.slot (-48) = cA ∧
    σ.slot (-40) = m

variable (lab : Label → Int64) (cP : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
  (cA m : BitVec 64)

/-- **The refusal path's nodes at `MSS`** (`fN`'s). -/
def fNS : FN → ND
  | .ts => ⟨lab x25L + 96, oP, fun σ c => c = cP ∧ CloneRef (σ.regs.get64 .rax) ∧ MSS sl cA m σ⟩
  | .je => ⟨lab x25L + 99, oP, fun σ c => c = cP ∧ CloneRef (σ.regs.get64 .rax) ∧ MSS sl cA m σ ∧
      σ.status.zf = false⟩
  | .x26 => ⟨lab x26L, oP, fun σ c => c = cP ∧ CloneRef (σ.regs.get64 .rax) ∧ MSS sl cA m σ⟩
  | .fl => ⟨lab flL, oP, fun σ c => c = cP ∧ MSS sl cA m σ⟩

/-- **The exit at `MSS`**: the call of `scc_rt_abort` with `%rdi = 5` and
the return address `raT lab ".Lwc_main"` at `-136`. -/
def fES : ND :=
  ⟨lab "scc_rt_abort", ⟨-136, [(.rbp, 0)]⟩, fun σ c => c = cP ∧ σ.regs.get64 .rdi = 5#64 ∧
    σ.slot (-136) = raT lab ".Lwc_main" ∧ MSS sl cA m σ⟩

/-! ## The segment -/

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {cP : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
  {cA m : BitVec 64}

/-- **Main after a refused clone is one segment inside `W`**, from `fNS .ts`
to the call of `scc_rt_abort(5)` (`fES`): `ZF` clear (a refusal is not `0`),
the `je` not taken, the `jl` taken (a refusal is negative), `.spawnfail5`'s
`call`. -/
theorem seg_failWS {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : failIn cells = true) {W : Frag isa} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -136) (hhi : 16 ≤ R.hi)
    (hWts : NodeW W K exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .ts))
    (hWje : BlkW W K exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .je) jeB)
    (hWx26 : BlkW W K exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .x26) x26B)
    (hWfl : BlkW W K exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .fl) flB) :
    SegW W K p lbl ms (At exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .ts))
      (At exe endPc R F (fES (_root_.Executable.labels exe).label cP sl cA m)) := by
  simp only [failIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨bts, bje⟩, hgap⟩, b26⟩, bfl⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have hg : lab x26L = lab x25L + Int64.ofNat 101 := label_labelGap_lays hp hgap
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)}, blockAt cells l k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have code0 : ∀ {l : Label} {k : Nat} {b : List (Directive × Nat)}, blockAt cells l k 0 b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab l) b :=
    fun h s he hn => by simpa using code h s he hn
  refine (fn_segW (N := fNS lab cP sl cA m) (E := fun _ : Unit => fES lab cP sl cA m) (fun i => ?_)
    FN.ts).mono_post fun _ _ ⟨_, h⟩ => h
  cases i
  case ts =>
    refine test_ndW hF (fun s he hn => code bts s he hn) hWts fun σ c hJ af =>
      ⟨c, .refl c, .inl ⟨FN.je, ?_, rfl, ?_⟩⟩
    · show lab x25L + 99 = lab x25L + Int64.ofNat 96 + Int64.ofNat 3
      rw [Int64.add_assoc]; rfl
    · obtain ⟨hc, hr, hms⟩ := hJ
      refine ⟨hc, hr, hms, ?_⟩
      rw [testStep_zf, BitVec.and_self]
      simpa only [beq_eq_false_iff_ne, ne_eq] using hr.ne_zero
  case je =>
    refine seg_ndW (by simp [jeB]) jeB_ok hF hR (by omega) hhi (fun s he hn => code bje s he hn) hWje
      fun σ c hJ => ⟨c, .refl c, .inl ⟨FN.x26, ?_, rfl, hJ.1, hJ.2.1, hJ.2.2.1⟩⟩
    obtain ⟨-, -, -, hz⟩ := hJ
    show lab x26L = (arun lab jeB ⟨lab x25L + 99, oP, σ⟩).pc
    rw [jeB_run]
    simp only [hz, hg, Bool.false_eq_true, ite_false, Int64.add_assoc]; rfl
  case x26 =>
    refine seg_ndW (by simp [x26B]) x26B_ok hF hR (by omega) hhi (fun s he hn => code0 b26 s he hn) hWx26
      fun σ c hJ => ⟨c, .refl c, .inl ⟨FN.fl, ?_, rfl, ?_⟩⟩
    · obtain ⟨-, hr, -⟩ := hJ
      have hm : σ.regs.rax.toBitVec.msb = true := by
        have := hr.slt; simpa [BitVec.slt_zero_eq_msb] using this
      show lab flL = (arun lab x26B ⟨lab x26L, oP, σ⟩).pc
      rw [x26B_run]; simp only [hm, ite_true]
    · obtain ⟨rfl, -, h8, h24, h32, h48, h40⟩ := hJ
      show c = c ∧ MSS sl cA m (arun lab x26B ⟨lab x26L, oP, σ⟩).σ
      rw [x26B_run]
      exact ⟨rfl, by simp [upd, h8], by simp [upd, h24], by simp [upd, h32], by simp [upd, h48],
        by simp [upd, h40]⟩
  case fl =>
    refine seg_ndW (by simp [flB]) flB_ok hF hR hlo hhi (fun s he hn => code0 bfl s he hn) hWfl
      fun σ c hJ => ⟨c, .refl c, .inr ⟨(), ?_, ?_, ?_⟩⟩
    · show lab "scc_rt_abort" = (arun lab flB ⟨lab flL, oP, σ⟩).pc
      rw [flB_run]
    · show SO.le ⟨-136, [(.rbp, 0)]⟩ (arun lab flB ⟨lab flL, oP, σ⟩).so = true
      rw [flB_run]; rfl
    · obtain ⟨rfl, h8, h24, h32, h48, h40⟩ := hJ
      show c = c ∧ (arun lab flB ⟨lab flL, oP, σ⟩).σ.regs.get64 .rdi = 5#64 ∧
        (arun lab flB ⟨lab flL, oP, σ⟩).σ.slot (-136) = raT lab ".Lwc_main" ∧
        MSS sl cA m (arun lab flB ⟨lab flL, oP, σ⟩).σ
      rw [flB_run]
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp (disch := decide) only [Reg64s.get64_set64_self, Reg64s.get64_set64_ne]
      · simp only [upd_apply, ↓reduceIte, raT, Int64.toBitVec_add]; rfl
      · simp [upd, h8]
      · simp [upd, h24]
      · simp [upd, h32]
      · simp [upd, h48]
      · simp [upd, h40]

/-- **Main after a refused clone does not return**: `seg_failWS`, then the
call of `scc_rt_abort(5)` (`seg_jabort5W`, the dispatcher in `[-24, 16)`
below the pushed return address at `-136`, the return address
`raT lab ".Lwc_main"`), given the threads abort path's obligations there per
caller state (`hstub`). -/
theorem seg_spawnFailWS {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : failIn cells = true)
    {W : Frag isa} {K : State → State → Prop} {Q : Frag isa}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -168) (hhi : 16 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hWts : NodeW W K exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .ts))
    (hWje : BlkW W K exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .je) jeB)
    (hWx26 : BlkW W K exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .x26) x26B)
    (hWfl : BlkW W K exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .fl) flB)
    (hstub : ∀ m0 σC c0, (fES (_root_.Executable.labels exe).label cP sl cA m).J σC c0 →
      Abort.Disp.StubTW W K p lbl ms exe endPc (R.callee (-136 - 8) (-24) 16)
        (fun m' => F m' ∧ CKept R (-136 - 8) (-24) 16 m0 m' ∧ Abs R ⟨-136, [(.rbp, 0)]⟩ m0 σC) c0
        (raT (_root_.Executable.labels exe).label ".Lwc_main")) :
    SegW W K p lbl ms (At exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .ts)) Q :=
  (seg_failWS hp hend hin hF hR (by omega) hhi hWts hWje hWx26 hWfl).seq
    (Abort.Disp.seg_jabort5W (nC := fES (_root_.Executable.labels exe).label cP sl cA m) rfl
      (fun σ c h => h.2.1) (fun σ c h => h.2.2.1) hF hR (by show R.lo ≤ -136 - 32; omega)
      (by show (-136 : Int) + 8 ≤ R.hi; omega) (by show (-136 : Int) % 8 = 0; decide) hK hstub)

/-- **`seg_spawnFailWS` in any valid layout of `helloCells`**: the blocks'
places decided (`hello_failIn`). -/
theorem seg_spawnFailWS_hello {kp : Nat} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp)
    {W : Frag isa} {K : State → State → Prop} {Q : Frag isa}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -168) (hhi : 16 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hWts : NodeW W K exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .ts))
    (hWje : BlkW W K exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .je) jeB)
    (hWx26 : BlkW W K exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .x26) x26B)
    (hWfl : BlkW W K exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .fl) flB)
    (hstub : ∀ m0 σC c0, (fES (_root_.Executable.labels exe).label cP sl cA m).J σC c0 →
      Abort.Disp.StubTW W K p lbl ms exe endPc (R.callee (-136 - 8) (-24) 16)
        (fun m' => F m' ∧ CKept R (-136 - 8) (-24) 16 m0 m' ∧ Abs R ⟨-136, [(.rbp, 0)]⟩ m0 σC) c0
        (raT (_root_.Executable.labels exe).label ".Lwc_main")) :
    SegW W K p lbl ms (At exe endPc R F (fNS (_root_.Executable.labels exe).label cP sl cA m .ts)) Q :=
  seg_spawnFailWS hp hend hello_failIn hF hR hlo hhi hK hWts hWje hWx26 hWfl hstub

end Seg

end Spike.Lib.X64.Flow.Worker.Hello.SpawnFail

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.seg_failWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.seg_failWS

/--
info: 'Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.seg_spawnFailWS_hello' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.seg_spawnFailWS_hello
