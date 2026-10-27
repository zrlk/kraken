/-
**The AArch64 consumer at any call depth from the user function's
interface** for an `Accepted1` program with calls (the twin of
`Spike/Lib/LowerX64/StartCorrectS.lean`): `a64_start_segWSG`
(`Spike/Lib/LowerA64/StartSegSG.lean`, `_start`'s segment inside `SFactsS`)
closed by `a64_lower_correctES_rtF` (`Spike/Lib/LowerA64/CorrectS.lean`),
the placement's facts discharged as in `a64_lower_correctE1`.

- `ovfDt_noWrite1`: at a system call, the overflow stub's write tail is no
  `write` to the output (fd `1`): the stub's `write` goes to fd `2`, the
  exit call is `exit_group`, and the other tail positions are not system
  calls (their cells, `Abort.Code`);
- `hroomU_ofPlaceOK'`: `hroomU_ofPlaceOK` for any user frame up to `12240`
  (the first stack's `16384` bytes less the guard's `4096` and
  `scc_rt_main`'s frame of `48`);
- `a64_lower_correctES_of_user`: `Correct` from the user function's
  `UserCallWS` inside `SFactsS` (`hU`) at a depth `D` and limit room `ZU`
  (`hD0`, `hD8`, `hD`, `hroomU`).
-/
import Spike.Lib.LowerA64.CorrectS
import Spike.Lib.LowerA64.StartSegSG
import Spike.Lib.LowerA64.TailBare
import Spike.Lib.LowerProgC1Core

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Sem
open Scc.Sem.A64 (abi pcOf atSvc_false_of_cellAt)
open Spike.Lib.A64Consumer (Lbl Lsize msOf TParE)
open Spike.Lib.A64ConsumerS (SFactsS msOfS msAgree_msOfS)
open Spike.Lib.A64.Rt (RuntimeLayout rtF entryR bareMC)
open Spike.Lib.A64.Flow.Ret0 (limA)
open Spike.Lib.A64.PhRec (μ K rtFree_ofPlaceOK hGh_ofPlaceOK hGf_ofPlaceOK hGt_ofPlaceOK hG1_ofPlaceOK
  hG0_ofPlaceOK hGn_ofPlaceOK hroomM_ofPlaceOK hownT_ofPlaceOK hownL_ofPlaceOK hownF_ofPlaceOK hownN_ofPlaceOK
  hmph_ofPlaceOK hsw_ofPlaceOK)
open Scc.Cert.Rt.A64.Print (add4 add0)

/-! ## The write tail writes no output -/

/-- **The overflow stub's write tail is no `write` to the output** at a
system call: at the stub's `write` `x0` is `2`; at the exit call `x8` is
`94` (`exit_group`); the spill and the two `movz` are not system calls
(their cells, `hcode`). -/
theorem ovfDt_noWrite1 {exe : _root_.Executable} {endPc : Int64} {lab : Label → Int64} {c0 : Ctl}
    (hcode : Abort.Code Abort.overflow c0 Abort.b1Overflow exe endPc)
    (hlab : (_root_.Executable.labels exe).label = lab) :
    ∀ s, OvfDt exe endPc lab s → abi.atSys s = true → ∀ buf n,
      Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n) := by
  subst hlab
  rintro s ⟨he, hn, hc⟩ hat buf n hd
  rcases hc with ⟨-, h0, h8, -⟩ | ⟨hpc, -⟩ | hpc | hpc | ⟨-, h8⟩
  · obtain ⟨buf', n', hd'⟩ := Spike.Lib.A64.StubW.svcCall_write h0 h8
    have hd'' : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 2 buf' n') := hd'
    rw [hd''] at hd
    simp at hd
  · have hc := (hcode.n5 s he hn).cell (j := 0) rfl rfl rfl (by rw [add0]; exact hpc)
    have hf : abi.atSys s = false := atSvc_false_of_cellAt hc (by intro _ h; cases h)
    rw [hf] at hat
    cases hat
  · have hc := (hcode.n5 s he hn).cell (j := 1) rfl rfl rfl (by rw [hpc]; simp only [Abort.N, add4, add0])
    have hf : abi.atSys s = false := atSvc_false_of_cellAt hc (by intro _ h; cases h)
    rw [hf] at hat
    cases hat
  · have hc := (hcode.n5 s he hn).cell (j := 2) rfl rfl rfl (by rw [hpc]; simp only [Abort.N, add4, add0])
    have hf : abi.atSys s = false := atSvc_false_of_cellAt hc (by intro _ h; cases h)
    rw [hf] at hat
    cases hat
  · have hd' : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup s.st.1.regs.X0.toNat) :=
      svcCall_exitGroup (by rw [h8]; rfl)
    rw [hd'] at hd
    cases hd

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

/-- The canonical load's memory. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (RuntimeLayout.ofPlaceOK h i).Λ o.prog o.secs

/-- **A user frame's room up to `12240`** (`hroomU_ofPlaceOK` without its
`4095` bound): the limit `stacksA + 4096` is below the first stack's top
less `scc_rt_main`'s frame and the user frame. -/
theorem hroomU_ofPlaceOK' :
    ∀ {frame : Int}, 0 ≤ frame → frame ≤ 12240 →
      ∀ v : Val, Spike.Lib.A64.PhRec.GOf Ly M0 ⟨limA (UInt64.ofBitVec ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
        (v.setWidth 64).toNat ≤
          (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - Spike.Lib.A64.Rt.bareMC.Z.toBitVec -
            (Int64.ofInt frame).toBitVec).toNat := by
  intro frame h0 h1
  refine Spike.Lib.A64.PhRec.room_of_le h i ?_
  have hf : (Int64.ofInt frame).toBitVec.toNat = frame.toNat := by
    rw [Int64.toBitVec_ofInt, BitVec.toNat_ofInt]
    omega
  rw [Spike.Lib.A64.PhRec.stacksA_lab h i, BitVec.toNat_sub, BitVec.toNat_sub,
    Spike.Lib.A64.Rt.top0_toNat (RuntimeLayout.ofPlaceOK h i), hf]
  have := (Ly).pool_fit
  obtain ⟨h1', h2'⟩ := (Ly).stacks_sub
  simp only at h1' h2'
  rw [show (Spike.Lib.A64.Rt.bareMC.Z.toBitVec).toNat = 48 from rfl]
  omega

end Place

section Correct

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)

/-- The facts every pair of the run carries at its frames, at the arena's
`cells` and the overflow stub's write tail. -/
local notation "WSS" h:max cells:max => fun s c fs => SFactsS (Ly h).Λ (μ (Ly h)) p
  (fun s _ => Spike.Lib.A64.PhRec.own (Ly h) s) (Spike.Lib.A64.Rt.rS0 (Ly h)) (Spike.Lib.A64.PhRec.Tk (Ly h))
  (Ly h).Λ.static cells 0 s c fs (OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab)

/-- The placement's memory side at the frames. -/
local notation "MSS" h:max G:max => msOfS (Ly h).Λ (μ (Ly h)) (fun _ => True) G
  (fun s _ => Spike.Lib.A64.PhRec.own (Ly h) s) (Ly h).Λ.static (fun _ => 0)

/-- The value invariant: the first TCB's limit word holds its loaded value or the limit. -/
local notation "G0" h:max => Spike.Lib.A64.PhRec.GOf (Ly h) (Spike.Lib.A64.PhRec.m0Of (Ly h).Λ (O).prog (O).secs)

/-- The outside move: the take of the first stack. -/
local notation "KS" h => K (Ly h) (Spike.Lib.A64.Rt.rS0 (Ly h))

/-- **The output of an `Accepted1` program has a bare tail**: `main` takes
`Unit`, so no setup block runs before it. -/
theorem tail_bare_of_accepted1 (hp : Scc.Lower.Accepted1 p = true) {em : Scc.Lower.A64.Emitted}
    (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em) : (O).place.tail = .bare := by
  have he : Scc.Lower.A64.lowerAll cfg p = em := by simp [Scc.Lower.A64.lowerAll, hlow]
  rw [he]
  unfold Scc.Lower.A64.lowerAll? at hlow
  cases hl : Scc.Lower.lowerIR cfg p with
  | error e => rw [hl] at hlow; cases hlow
  | ok l =>
    rw [hl] at hlow
    have hlow : Scc.Lower.A64.emitAll l = .ok em := hlow
    have hlo := (Scc.Lower.A64.emitAll_frames hlow).1
    have hc := lowerIR_checked hl
    rw [Spike.Lib.LowerNode.checkedOf_accepted1 hp] at hc
    have hc' := (Except.ok.inj hc).symm
    simp only [Out.ofEmitted, placeDataOf, hlo, hc']
    rfl

/-- **The AArch64 consumer at any call depth from the user function's
interface**: for an `Accepted1` program `p` lowered to `em` (`hlow`) whose
output passes the placement check (`h`) with no static label (`hs`), at an
admissible entry state `E` (`hE`), given the user function `main`'s
`UserCallWS` inside `SFactsS` at the budget's arena and the overflow stub's
write tail (`hU`, for every switch value) at a depth `D` (`hD0`, `hD8`,
`hD`) and limit room `ZU` (`hroomU`), the output is `Correct` over the
target on parsed texts at `E`. -/
theorem a64_lower_correctES_of_user (hp : Scc.Lower.Accepted1 p = true) {em : Scc.Lower.A64.Emitted}
    (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em) {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (O) = true) (hs : ∀ l, Λ.static l = none) {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    {E : Entry} (hE : E.Ok (Ly h).Λ)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hD : D + 48 ≤ 16384) {ZU : Int64}
    (hroomU : ∀ v : Val, (G0 h) ⟨limA (UInt64.ofBitVec ((Ly h).pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64 - bareMC.Z.toBitVec - ZU.toBitVec).toNat)
    (hU : ∀ v, Spike.Lib.A64.Rt.UserCallWS (WSS h B.cells) (KS h) p (Ly h).Λ.static (MSS h (G0 h))
      (Ly h).exe (Ly h).endPc (swR v (-(D + 48)) 0)
      (Spike.Lib.A64.Rt.swFSL (D + 48) (Spike.Lib.A64.Rt.rS0 (Ly h)) (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (Ret0.pinA (Ly h).lab + 0#64 + 8#64))) v)
      bareMC.fn bareMC.Z D ZU (UPostS p (Ly h).Λ.static Spike.Lib.A64Consumer.c0)
      ((Ly h).lab bareMC.e0 + 4).toBitVec Spike.Lib.A64Consumer.c0
      (UInt64.ofBitVec (Ret0.pinA (Ly h).lab + 0#64 + 8#64))) :
    Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) p) (Ly h).Λ B
      ((O).prog, (O).secs) := by
  have hs' : (Ly h).Λ.static = fun _ => none := funext hs
  have htl := tail_bare_of_accepted1 hp hlow
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of p) (rS := Spike.Lib.A64.Rt.rS0 (Ly h))
  have hsd := abortIn_of_placeOKAt h
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hcode := Scc.Cert.Rt.A64.Abort.code_stub (c0 := Spike.Lib.A64Consumer.c0) hI.lays hI.endOk hsd.1.1.1.1.1
  exact a64_lower_correctES_rtF hp h hs hE
    (a64_start_segWSG h (Scc.Lower.imms1Of p) htl hp (Spike.Lib.good1_tail rfl) msOfS_nil msAgree_msOfS
      (ovfDt_noWrite1 hcode hI.labOk) (hs' ▸ rtFree_ofPlaceOK h _) hE hD0 hD8 hD
      (hGh_ofPlaceOK h _) (hGf_ofPlaceOK h _) (hGt_ofPlaceOK h _) (hownT_ofPlaceOK h _) (hG1_ofPlaceOK h _)
      (hG0_ofPlaceOK h _) (hGn_ofPlaceOK h _) (hownL_ofPlaceOK h _) (hownF_ofPlaceOK h _) (hownN_ofPlaceOK h _)
      (hroomM_ofPlaceOK h _) hroomU Ret0.Inst.cfacts_c0
      (hmph_ofPlaceOK h _ htl) (hsw_ofPlaceOK h _)
      (fun _ h => h) (Spike.Lib.A64.Rt.rtF_stable _ hE)
      (fun _ _ hm => Spike.Lib.A64.Rt.rtF_takeMem _ (Spike.Lib.A64.Rt.rS0_sub (Ly h)) hm) (U := fun _ => True)
      (fun _ _ => trivial) (fun _ _ _ _ => trivial)
      (Spike.Lib.A64.Rt.entryW_ofPlaceOK h _ (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE)
        (by show (-65536 : Int) ≤ 0; decide) (by show (0 : Int) ≤ 0; decide) Ret0.Inst.cfacts_c0)
      fun v => by
        have he : (fun m => Spike.Lib.A64.Rt.swFSL (D + 48) (Spike.Lib.A64.Rt.rS0 (Ly h))
            (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64)
            (limA (UInt64.ofBitVec (Ret0.pinA (Ly h).lab + 0#64 + 8#64))) v m ∧ True) =
          Spike.Lib.A64.Rt.swFSL (D + 48) (Spike.Lib.A64.Rt.rS0 (Ly h)) (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64)
            (limA (UInt64.ofBitVec (Ret0.pinA (Ly h).lab + 0#64 + 8#64))) v :=
          funext fun _ => and_true _
        rw [he]; exact hU v)

end Correct

end Spike.Lib.LowerA64
