/-
**`scc_rt_thread_init`'s states inside `W`, for any program** (`tiW_gen`):
the obligations `TiW` (`Spike/Lib/A64Ret0.lean`) of every node of
`scc_rt_thread_init`, from an instance's facts (`InstOk`), the function's
code (`threadInitIn`, a field of `RtCodeIn`), its phase facts (`TiPh`), the
TCB's six words it writes, and at its call `scc_rt_stack_take`'s premises
(`takeW_gen`) in the callee's region.

- **The phase facts** (`TiPh`): each block's phase check at its pc
  (`blkPh`, the rows of `RtNodesOk`, A6), no dead target; each store off
  the sites and in its next pc's phase; the prologue and the call not in
  the take's phase.
- **The words**: the TCB's six fields `tcb + 8·j` (`tiAddrs`) mapped in the
  loaded kernel state, unmapped in private memory under the frame condition
  and owned at no phase.
- **Oracle**: `ret0.w`'s `tiW` (`Spike/Lib/A64Ret0I.lean`) without its take
  site premise is this at its instance (`Spike/Test/A64RtTi.lean`).
-/
import Spike.Lib.Rt.A64RtTake

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (TI TiG TiW tiN tiTake lockA freeNA nextA stacksA StackM rAddr_x10)
open Scc.Cert.Rt.A64 (blockAt)

namespace Ti

open Spike.Lib.A64.Flow.Ret0.ThreadInit

/-- The TCB's six fields' addresses `tcb + 8·j`. -/
def tiAddrs (tcb : BitVec 64) : List (BitVec 64) :=
  [tcb + BitVec.ofNat 64 (8 * 0), tcb + BitVec.ofNat 64 (8 * 1), tcb + BitVec.ofNat 64 (8 * 2),
    tcb + BitVec.ofNat 64 (8 * 3), tcb + BitVec.ofNat 64 (8 * 4), tcb + BitVec.ofNat 64 (8 * 5)]

/-- The stores' pcs. -/
def stPcs (lab : Label → Int64) : List Int64 :=
  [storePc lab 0, storePc lab 1, storePc lab 2, storePc lab 3, storePc lab 4, storePc lab 5]

/-- **`scc_rt_thread_init`'s phase facts** at labels `lab`, phase index
`ph`, off-site pcs `okPc`, returning to `ra spL`. -/
structure TiPh (okPc : Nat → Bool) (ph : Nat → Nat) (Tk : State → Prop) (lab ra : Label → Int64) : Prop where
  e : blkPh okPc ph (fun _ => false) lab (lab fnL + Int64.ofNat (4 * 0)) (ra fnL) tiPro = true
  entry : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat (4 * 0)) (ra entryL) tiCall = true
  sp : blkPh okPc ph (fun _ => false) lab (lab spL + Int64.ofNat (4 * 0)) (ra spL) tiSp = true
  f1 : blkPh okPc ph (fun _ => false) lab (lab spL + Int64.ofNat (4 * 12)) (ra spL) tiF1 = true
  f2 : blkPh okPc ph (fun _ => false) lab (lab spL + Int64.ofNat (4 * 15)) (ra spL) tiF2 = true
  f3 : blkPh okPc ph (fun _ => false) lab (lab spL + Int64.ofNat (4 * 18)) (ra spL) tiF3 = true
  f4 : blkPh okPc ph (fun _ => false) lab (lab spL + Int64.ofNat (4 * 21)) (ra spL) tiF4 = true
  f5 : blkPh okPc ph (fun _ => false) lab (lab spL + Int64.ofNat (4 * 24)) (ra spL) tiF5 = true
  ret : blkPh okPc ph (fun _ => false) lab (lab spL + Int64.ofNat (4 * 27)) (ra spL) tiRet = true
  st : ∀ p ∈ stPcs lab, okPc p.toBitVec.toNat = true ∧ ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat
  noTk : ∀ p ∈ [lab fnL + Int64.ofNat (4 * 0), lab entryL + Int64.ofNat (4 * 0)], ∀ s : State,
    pcOf s = p.toBitVec.toNat → ¬ Tk s

theorem tiPro_noRet : noRetBlk tiPro = true := by rfl
theorem tiCall_noRet : noRetBlk tiCall = true := by rfl
theorem tiSp_noRet : noRetBlk tiSp = true := by rfl
theorem tiF1_noRet : noRetBlk tiF1 = true := by rfl
theorem tiF2_noRet : noRetBlk tiF2 = true := by rfl
theorem tiF3_noRet : noRetBlk tiF3 = true := by rfl
theorem tiF4_noRet : noRetBlk tiF4 = true := by rfl
theorem tiF5_noRet : noRetBlk tiF5 = true := by rfl

/-! The stores' code, `str x9, [x10, #8·j]`. -/

theorem st0_eq : parseAArch64("str x9, [x10]") = [strDir .X9 .X10 (Int64.ofNat (8 * 0))] := by decide
theorem st1_eq : parseAArch64("str x9, [x10, #8]") = [strDir .X9 .X10 (Int64.ofNat (8 * 1))] := by decide
theorem st2_eq : parseAArch64("str x9, [x10, #16]") = [strDir .X9 .X10 (Int64.ofNat (8 * 2))] := by decide
theorem st3_eq : parseAArch64("str x9, [x10, #24]") = [strDir .X9 .X10 (Int64.ofNat (8 * 3))] := by decide
theorem st4_eq : parseAArch64("str x9, [x10, #32]") = [strDir .X9 .X10 (Int64.ofNat (8 * 4))] := by decide
theorem st5_eq : parseAArch64("str x9, [x10, #40]") = [strDir .X9 .X10 (Int64.ofNat (8 * 5))] := by decide

end Ti

set_option hygiene false in
/-- A store of a TCB field of `scc_rt_thread_init`, after the take. -/
local macro "tst " b:term:max j:term:max : tactic =>
  `(tactic| focus
    dsimp only [TiW]; rw [hI.labOk]
    have hs := hph.st (storePc lab $j) (by simp [stPcs])
    have ha : q.tcb + BitVec.ofNat 64 (8 * $j) ∈ tiAddrs q.tcb := by simp [tiAddrs]
    exact nodeW_st_post hI hown $b rfl rfl (hC _ fun _ _ hJ => hJ.1) hs.1 hs.2
      (fun σ _ hJ => by rw [rAddr_x10 hJ.2.2.2]; rfl) (hmF _ ha) (hunF _ ha) (hnoF _ ha) hsub)

set_option maxHeartbeats 800000 in
open Ti Take Spike.Lib.A64.Flow.Ret0.ThreadInit in
/-- **`scc_rt_thread_init`'s states are inside `SFacts`**, for any program
with the function's code (`hin`), in any region holding its frame and the
take's below, with the source control `c0` (`hC0`, its facts), returning to
`ra spL` (`hra`), its phase facts (`hph`), the TCB's six words mapped
(`hmF`), unmapped in private memory under the frame condition (`hunF`) and
owned at no phase (`hnoF`), the take's range in the pool (`hsub`) kept by
the writes of both regions (`hSM`, `hSM'`), and at its call
`scc_rt_stack_take`'s premises of `takeW_gen` (`hin'` to `hdisj`), returning
to `.sp0`. -/
theorem tiW_gen {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {c0 : Ctl} {F : MachineData → Prop}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : threadInitIn prog = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi) (q : TiG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra spL).toBitVec) (hph : TiPh okPc ph Tk lab ra)
    (hmF : ∀ a ∈ tiAddrs q.tcb, Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hunF : ∀ a ∈ tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hnoF : ∀ a ∈ tiAddrs q.tcb, ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS))
    (hSM' : FStable (R.callee oI.sp (-208) 0) (StackM rS))
    (hin' : Ret0.StackTake.stackTakeIn prog = true) (hphT : TakePh okPc ph Tk ownOf μ lab fun _ => lab spL)
    (hmL : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨lockA lab, 8⟩ = true)
    (hmN : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨freeNA lab, 8⟩ = true)
    (hmX : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨nextA lab, 8⟩ = true)
    (hunL : ∀ m, F m → Mem.loadInt m.dmem (lockA lab) 8 = none)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (freeNA lab) 8 = none)
    (hunX : ∀ m, F m → Mem.loadInt m.dmem (nextA lab) 8 = none)
    (hrS : rS = ⟨(stacksA lab + q.k0).toNat, 16384⟩) (hdisj : Λ.rodata.Disjoint Λ.stackPool) :
    ∀ i, TiW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (StackM rS) q i := by
  have h := hin
  simp only [threadInitIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bSp⟩, bS0⟩, bF1⟩, bS1⟩, bF2⟩, bS2⟩, bF3⟩, bS3⟩, bF4⟩, bS4⟩, bF5⟩, bS5⟩,
    bRet⟩ := h
  rw [st0_eq] at bS0; rw [st1_eq] at bS1; rw [st2_eq] at bS2
  rw [st3_eq] at bS3; rw [st4_eq] at bS4; rw [st5_eq] at bS5
  have hC : ∀ (n : ND), (∀ σ c, n.J σ c → c = q.c0) → ∀ σ c, n.J σ c → CFacts Λ lbl c :=
    fun _ hn σ c hJ => (hn σ c hJ).trans hq ▸ hC0
  have hnr : ∀ {blk : List Directive}, noRetBlk blk = true → ∀ {n : ND} {ra' : Int64}, ∀ σ c, n.J σ c →
      ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra' :=
    fun hb _ _ _ _ _ k hk r hr => (noRet_false hb k hk r hr).elim
  intro i
  cases i
  case e =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_pre hI bE (ofNat4_zero _) tiPro_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.e
      (hnr tiPro_noRet) (fun _ _ _ => rfl) (hph.noTk _ (by simp))
  case entry =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_pre hI bEn (ofNat4_zero _) tiCall_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1)
      hph.entry (hnr tiCall_noRet) (fun _ _ _ => rfl) (hph.noTk _ (by simp))
  case call =>
    intro g hg j
    rw [hI.labOk] at hg
    have hlo' : R.lo ≤ oI.sp + -208 := by show R.lo ≤ -48 + -208; omega
    have hkc : oI.sp < R.hi := by show (-48 : Int) < R.hi; omega
    have hR' := Region.callee_ok (hi' := 0) hR hlo' (by decide) hkc (by show (-48 : Int) + 0 ≤ R.hi; omega)
    have hb' := Region.callee_base (hi' := 0) hR hlo' (by decide) hkc
    have hal' : (R.callee oI.sp (-208) 0).base.toNat % 16 = 0 := by
      have : (((R.callee oI.sp (-208) 0).base.toNat : Int)) % 16 = 0 := by
        rw [hb']; show ((R.base.toNat : Int) + -48) % 16 = 0; omega
      omega
    exact takeW_gen hI hown hin' hC0 hR' hal' (by show (-208 : Int) ≤ -208; omega) (by show (0 : Int) ≤ 0; omega)
      (tiTake q g) hq hg hphT hmL hmN hmX hunL hunN hunX hrS hsub hdisj hSM' j
  case sp =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_post hI bSp (ofNat4_zero _) tiSp_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.sp
      (hnr tiSp_noRet) (fun _ _ _ => rfl) hsub hSM
  case st0 => tst bS0 0
  case f1 =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_post hI bF1 rfl tiF1_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.f1
      (hnr tiF1_noRet) (fun _ _ _ => rfl) hsub hSM
  case st1 => tst bS1 1
  case f2 =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_post hI bF2 rfl tiF2_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.f2
      (hnr tiF2_noRet) (fun _ _ _ => rfl) hsub hSM
  case st2 => tst bS2 2
  case f3 =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_post hI bF3 rfl tiF3_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.f3
      (hnr tiF3_noRet) (fun _ _ _ => rfl) hsub hSM
  case st3 => tst bS3 3
  case f4 =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_post hI bF4 rfl tiF4_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.f4
      (hnr tiF4_noRet) (fun _ _ _ => rfl) hsub hSM
  case st4 => tst bS4 4
  case f5 =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_post hI bF5 rfl tiF5_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.f5
      (hnr tiF5_noRet) (fun _ _ _ => rfl) hsub hSM
  case st5 => tst bS5 5
  case ret =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_post hI bRet rfl tiRet_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.ret
      (hret_of_run tiRet_ok fun _ _ hJ => by
        dsimp only [tiN] at hJ ⊢
        rw [(tiRet_walk lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) hsub hSM

end Spike.Lib.A64.Rt
