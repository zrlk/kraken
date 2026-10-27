/-
**The x86-64 consumer at any call depth from the user function's
interface** for an `Accepted1` program with calls: `x64_start_segWSG`
(`Spike/Lib/LowerX64/StartSegSG.lean`, `_start`'s segment inside `SFactsS`)
closed by `x64_lower_correctES_rtF` (`Spike/Lib/LowerX64/CorrectS.lean`),
the placement's facts discharged as in `x64_lower_correctE1`.

- `ovfDt_noWrite1`: at a system call, the overflow stub's write tail is no
  `write` to the output (fd `1`): the stub's `write` goes to fd `2`, the
  exit call is `exit_group`, and the other tail positions are not system
  calls (their cells, `Abort.Code`);
- `hroomU_ofPlaceOK'`: `hroomU_ofPlaceOK` for any user frame up to `12224`
  (the first stack's `16384` bytes less the guard's `4096` and the `64`
  bytes of `scc_rt_main`'s and the user call's return addresses, saved
  `%rbp`s and `scc_rt_main`'s frame);
- `x64_lower_correctES_of_user`: `Correct` from the user function's
  `UserCallWS` inside `SFactsS` (`hU`) at a depth `D` and limit room `ZU`
  (`hD0`, `hD8`, `hD`, `hroomU`).
-/
import Spike.Lib.LowerX64.CorrectS
import Spike.Lib.LowerX64.StartSegSG
import Spike.Lib.LowerProgC1Core

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Sem
open Scc.Sem.X64 (abi pcOf atSyscall_of_cellAt atSyscall_false_of_cellAt)
open Spike.Lib.X64Consumer (Lbl Lsize msOf TParE)
open Spike.Lib.X64ConsumerS (SFactsS msOfS msAgree_msOfS)
open Spike.Lib.X64.Rt (RuntimeLayout rtF entryR bareMC)
open Spike.Lib.X64.Flow.Ret0 (limA tpOf)
open Spike.Lib.X64.PhRec (μ K)
open Spike.Lib.X64.StubW (syscallCall_write)

/-! ## The write tail writes no output -/

/-- **The overflow stub's write tail is no `write` to the output** at a
system call: at the stub's `write` `%rdi` is `2`; at the exit call `%rax`
is `231` (`exit_group`); the spill and the two moves are not system calls
(their cells, `hcode`). -/
theorem ovfDt_noWrite1 {exe : _root_.Executable} {endPc : Int64} {lab : Label → Int64} {c0 : Ctl}
    (hcode : Abort.Code Abort.overflow c0 Abort.x1Overflow exe endPc)
    (hlab : (_root_.Executable.labels exe).label = lab) :
    ∀ s, OvfDt exe endPc lab s → abi.atSys s = true → ∀ buf n,
      Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n) := by
  subst hlab
  rintro s ⟨he, hn, hc⟩ hat buf n hd
  rcases hc with ⟨-, ha, h0, -⟩ | ⟨hpc, -⟩ | hpc | hpc | ⟨-, h231⟩
  · obtain ⟨buf', n', hd'⟩ := syscallCall_write ha h0
    have hd'' : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 2 buf' n') := hd'
    rw [hd''] at hd
    simp at hd
  · have hc := (hcode.n5 s he hn).cell (j := 0) rfl rfl rfl
      (by rw [show Int64.ofNat (cellOff Abort.x2 0) = 0 by decide, Int64.add_zero]; exact hpc)
    have hf : abi.atSys s = false := atSyscall_false_of_cellAt hc (by intro _ _ h; cases h)
    rw [hf] at hat
    cases hat
  · have hc := (hcode.n5 s he hn).cell (j := 1) rfl rfl rfl
      (by rw [hpc]; show _ = _ + 36 + _; rw [Int64.add_assoc]; rfl)
    have hf : abi.atSys s = false := atSyscall_false_of_cellAt hc (by intro _ _ h; cases h)
    rw [hf] at hat
    cases hat
  · have hc := (hcode.n5 s he hn).cell (j := 2) rfl rfl rfl
      (by rw [hpc]; show _ = _ + 36 + _; rw [Int64.add_assoc]; rfl)
    have hf : abi.atSys s = false := atSyscall_false_of_cellAt hc (by intro _ _ h; cases h)
    rw [hf] at hat
    cases hat
  · have hx : s.st.1.regs.rax.toNat = 231 := by
      simp only [Reg64s.get64] at h231
      rw [← UInt64.toNat_toBitVec, h231]; rfl
    have hd' : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup s.st.1.regs.rdi.toNat) :=
      Spike.Lib.X64.syscallCall_exitGroup hx
    rw [hd'] at hd
    cases hd

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

/-- The canonical load's memory. -/
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (RuntimeLayout.ofPlaceOK h i).Λ o.prog o.secs

/-- **A user frame's room up to `12224`** (`hroomU_ofPlaceOK` without its
`4096` bound): the limit `stacksA + 4096` is below the first stack's top
less `64` bytes and the frame. -/
theorem hroomU_ofPlaceOK' :
    ∀ {frame : Int}, 0 ≤ frame → frame ≤ 12224 →
      ∀ v : Val, Spike.Lib.X64.PhRec.GOf Ly M0 ⟨limA (tpOf ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
        (v.setWidth 64).toNat ≤ (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 -
          Spike.Lib.X64.Rt.bareMC.Z.toBitVec - 8#64 - 8#64 - (Int64.ofInt frame).toBitVec).toNat := by
  intro frame h0 h1
  refine Spike.Lib.X64.PhRec.room_of_le h i ?_
  have hf : (Int64.ofInt frame).toBitVec.toNat = frame.toNat := by
    rw [Int64.toBitVec_ofInt, BitVec.toNat_ofInt]
    omega
  rw [Spike.Lib.X64.PhRec.stacksA_lab h i]
  simp only [BitVec.toNat_sub, Spike.Lib.X64.Rt.top0_toNat (RuntimeLayout.ofPlaceOK h i), hf,
    show (Spike.Lib.X64.Rt.bareMC.Z.toBitVec).toNat = 32 from rfl, BitVec.toNat_ofNat]
  have := (Ly).pool_fit
  obtain ⟨h1', h2'⟩ := (Ly).stacks_sub
  simp only at h1' h2'
  omega

end Place

section Correct

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {sizes : List Nat}
  {labelOffs : List (String × Nat)}

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)

/-- The facts every pair of the run carries at its frames, at the arena's
`cells` and the overflow stub's write tail. -/
local notation "WSS" h:max cells:max => fun s c fs => SFactsS (Ly h).Λ (μ (Ly h)) p
  (fun s _ => Spike.Lib.X64.PhRec.own (Ly h) s) (Spike.Lib.X64.Rt.rS0 (Ly h)) (Spike.Lib.X64.PhRec.Tk (Ly h))
  (Ly h).Λ.static cells 0 s c fs (OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab)

/-- The placement's memory side at the frames. -/
local notation "MSS" h:max G:max => msOfS (Ly h).Λ (μ (Ly h)) (fun _ => True) G
  (fun s _ => Spike.Lib.X64.PhRec.own (Ly h) s) (Ly h).Λ.static (fun _ => 0)

/-- The value invariant: the first TCB's limit word holds its loaded value or the limit. -/
local notation "G0" h:max => Spike.Lib.X64.PhRec.GOf (Ly h) (Spike.Lib.X64.PhRec.m0Of (Ly h).Λ (O).prog (O).secs)

/-- The outside move: the take of the first stack. -/
local notation "KS" h => K (Ly h) (Spike.Lib.X64.Rt.rS0 (Ly h))

/-- **The x86-64 consumer at any call depth from the user function's
interface**: for an `Accepted1` program `p` lowered to `em` (`hlow`) whose
output passes the placement check (`h`) with no static label (`hs`), at an
admissible entry state `E` (`hE`), given the user function `main`'s
`UserCallWS` inside `SFactsS` at the budget's arena and the overflow stub's
write tail (`hU`, for every switch value and frame condition of the switch
region) at a depth `D` (`hD0`, `hD8`, `hD`) and limit room `ZU`
(`hroomU`), the output is `Correct` over the target on parsed texts at
`E`. -/
theorem x64_lower_correctES_of_user (hp : Scc.Lower.Accepted1 p = true) {em : Scc.Lower.X64.Emitted}
    (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em) {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (O) = true) (hs : ∀ l, Λ.static l = none) {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    {E : Entry} (hE : E.Ok (Ly h).Λ)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hD : D + 56 ≤ 16384) {ZU : Int64}
    (hroomU : ∀ v : Val, (G0 h) ⟨limA (tpOf ((Ly h).pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64 - 8#64 - 8#64 - bareMC.Z.toBitVec -
        8#64 - 8#64 - ZU.toBitVec).toNat)
    (hU : ∀ v (F' : MachineData → Prop),
      (∀ m, F' m → Spike.Lib.X64.Rt.swFSL (D + 56) (Spike.Lib.X64.Rt.rS0 (Ly h))
          (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64) (limA (tpOf (Ret0.pinA (Ly h).lab + 0#64 + 8#64))) v m ∧
        Ret0.CallerCells (swR v (-(D + 56)) 0) (-8 - 0) (8 - (D + 56)) 8 m) →
      Spike.Lib.X64.Rt.UserCallWS (WSS h B.cells) (KS h) p (Ly h).Λ.static (MSS h (G0 h)) (Ly h).exe
        (Ly h).endPc ((swR v (-(D + 56)) 0).callee (-8 - 0) (8 - (D + 56)) 8) F' bareMC.fn bareMC.Z D ZU
        (UPostS p (Ly h).Λ.static Spike.Lib.X64Consumer.c0)
        (((_root_.Executable.labels (Ly h).exe).label bareMC.sp0).toBitVec) Spike.Lib.X64Consumer.c0
        (tpOf (Ret0.pinA (_root_.Executable.labels (Ly h).exe).label + 0#64 + 8#64))) :
    Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) p) (Ly h).Λ B
      ((O).prog, (O).secs, (O).labelOffs) := by
  have hs' : (Ly h).Λ.static = fun _ => none := funext hs
  have htl := tail_bare_of_checked (Spike.Lib.LowerNode.checkedOf_accepted1 hp) hlow sizes labelOffs
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of p) (rS := Spike.Lib.X64.Rt.rS0 (Ly h))
  have hsd := hprog_ofPlaceOK h (Scc.Lower.imms1Of p)
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hcode := Scc.Cert.Rt.X64.Abort.code_stub (c0 := Spike.Lib.X64Consumer.c0) hI.lays hI.endOk hsd.1.1.1.1.1
  open Spike.Lib.X64.PhRec in
  exact x64_lower_correctES_rtF hp h hs hE
    (x64_start_segWSG h (Scc.Lower.imms1Of p) htl hp (Spike.Lib.good1_tail rfl) msOfS_nil msAgree_msOfS
      (ovfDt_noWrite1 hcode hI.labOk) (hs' ▸ rtFree_ofPlaceOK h _) hE hD0 hD8 hD
      (hGh_ofPlaceOK h _) (hGf_ofPlaceOK h _) (hGt_ofPlaceOK h _)
      (hownT_of_ph h _ (by rw [hphT_ofPlaceOK h _])) (hG1_ofPlaceOK h _) (hG0_ofPlaceOK h _)
      (hGn_ofPlaceOK h _) (hownL_of_ph h _ (by rw [hphL_ofPlaceOK h _])) (hownF_ofPlaceOK h _)
      (hownN_of_ph h _ (by rw [hphN_ofPlaceOK h _]))
      (hroomM_ofPlaceOK h _) hroomU Ret0.Inst.cfacts_c0
      (Spike.Lib.X64.Rt.PhRecOf.mainPh_bare_ofPlaceOK h _ htl) (Spike.Lib.X64.Rt.PhRecOf.swPh_ofPlaceOK h _)
      (fun _ h => h) (Spike.Lib.X64.Rt.rtF_stable _ hE)
      (fun _ _ hm => Spike.Lib.X64.Rt.rtF_takeMem _ (Spike.Lib.X64.Rt.rS0_sub (Ly h)) hm) (U := fun _ => True)
      (fun _ _ => trivial) (fun _ _ _ _ => trivial)
      (Spike.Lib.X64.Rt.entryW_ofPlaceOK h _ (Spike.Lib.X64.Rt.entryR_ok hE)
        (by show (-65536 : Int) ≤ -8; decide) (by show (0 : Int) ≤ 0; decide) Ret0.Inst.cfacts_c0)
      fun v F' hF' => hU v F' fun m hm => (hF' m hm).1)

end Correct

end Spike.Lib.LowerX64
