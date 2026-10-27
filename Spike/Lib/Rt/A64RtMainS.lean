/-
**`scc_rt_main` after a setup block, its states inside `SFacts`, for any
program** (`mainSW_sfacts`): the obligations `MainSW`
(`Spike/Lib/Rt/A64MainS.lean`) of `scc_rt_main`'s own nodes after a setup
block (the stack-checked prologue, `bl setup`, the marshalling block and
`bl fn`, the `exit_group` tail) as `mainUW_gen` (`Spike/Lib/Rt/A64RtMainU.lean`)
gives the bare shape's, from an instance's facts (`InstOk`), the code check
(`mainSIn`), the phase facts (`MainPhS`) and the limit word's facts.

- `MainPhS`: `scc_rt_main`'s phase facts at a setup code `sc`, the rows of
  `mainPhTabS sc`; `mainPhS_of_tab` from a checked table holding them,
  `mainPhS_of_placeOKAt` at an output passing `placeOK` with a setup block
  (A11, some `sw < 8`);
- `mainSW_ofFalse`: `MainSW` under an unsatisfiable frame condition;
- `mainSW_sfacts`: `MainSW` inside `SFacts`, with the source control's facts
  at the entry (`hC0`), after the setup block under `PostS` (`hPostS`) and
  at the return point under `Post` (`hPost`).
-/
import Spike.Lib.Rt.A64MainS
import Spike.Lib.Rt.A64RtPhRec
import Spike.Lib.LowerA64.SetupOfPlaceOK

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (MainG limA tcbA_limA StackOff)
open Scc.Cert.Rt.A64 (blockAt label_labelGap)

namespace MainS

/-- **`scc_rt_main`'s phase facts after a setup block at `sc`** at labels
`lab`, phase index `ph`, off-site pcs `okPc` (the rows of `mainPhTabS sc`):
the prologue's blocks, the setup call's, the marshalling block's and the
tail's at their pcs, no dead target; the limit's load and the `svc` off the
sites and in their next pc's phase. -/
structure MainPhS (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (sc : SetupCode) : Prop where
  hd : blkPh okPc ph (fun _ => false) lab (lab sc.sc + Int64.ofNat (4 * 0)) 0 (chkHead sc.Z) = true
  ld : okPc (lab sc.sc + Int64.ofNat (4 * 2)).toBitVec.toNat = true ∧
    ph (lab sc.sc + Int64.ofNat (4 * 2) + Int64.ofNat 4).toBitVec.toNat =
      ph (lab sc.sc + Int64.ofNat (4 * 2)).toBitVec.toNat
  br : blkPh okPc ph (fun _ => false) lab (lab sc.sc + Int64.ofNat (4 * 3)) 0 (chkBr sc.grow) = true
  fr : blkPh okPc ph (fun _ => false) lab (lab sc.sc + Int64.ofNat (4 * 5)) 0 (frameSet sc.Z [(.X0, 0)]) = true
  call0 : blkPh okPc ph (fun _ => false) lab (lab sc.e0 + Int64.ofNat (4 * 0)) 0 [blD sc.setup] = true
  sp0 : blkPh okPc ph (fun _ => false) lab (lab sc.sp0 + Int64.ofNat (4 * 0)) 0 (marshal sc.sw sc.fn) = true
  ex : blkPh okPc ph (fun _ => false) lab (lab sc.sp1 + Int64.ofNat (4 * 0)) 0 (exitTail sc.k) = true
  svc : okPc (lab sc.sp1 + Int64.ofNat (4 * 3)).toBitVec.toNat = true ∧
    ph (lab sc.sp1 + Int64.ofNat (4 * 3) + Int64.ofNat 4).toBitVec.toNat =
      ph (lab sc.sp1 + Int64.ofNat (4 * 3)).toBitVec.toNat

/-- The marshalling block has no `ret`. -/
theorem marshal_noRet (sw : Nat) (fn : Label) : noRetBlk (marshal sw fn) = true := by
  refine List.all_eq_true.mpr fun d hd => ?_
  simp only [marshal, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hd
  rcases hd with (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | (rfl | rfl)
  · have hc : Flow.classify (spStr (argX i) (Int64.ofNat (8 * (i + 1)))) =
        some (Flow.AI.str (.low (.reg (argX i)) .W64) (Int64.ofNat (8 * (i + 1)))) := rfl
    rw [hc]
  · have hc : Flow.classify (spLdr (argX i) (Int64.ofNat (8 * (i + 1)))) =
        some (Flow.AI.ldr (.low (.reg (argX i)) .W64) (Int64.ofNat (8 * (i + 1)))) := rfl
    rw [hc]
  · have hc : Flow.classify (spLdr (argX sw) 0) = some (Flow.AI.ldr (.low (.reg (argX sw)) .W64) 0) := rfl
    rw [hc]
  · simp [blD, Flow.classify]

end MainS

open MainS MainU

section Tab

open Spike.Lib.A64.Rt.PhOfTab
open Spike.Lib.A64.PhRec (ph okPc)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`scc_rt_main`'s phase facts after a setup block at `sc`** of a program
passing the table `mainPhTabS sc`. -/
theorem mainPhS_of_tab {sc : SetupCode}
    (hm : Scc.Cert.Rt.A64.rtPhOk (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog (RuntimeLayout.ofPlaceOK h i).Λ
      (mainPhTabS sc) = true) :
    MainPhS (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
      (RuntimeLayout.ofPlaceOK h i).lab sc := by
  have hf : ∀ f ∈ mainPhTabS sc, _ := fun f hf => Scc.Cert.Rt.A64.factOk_of_rtPhOk (f := f) hm hf
  have hl := PhRecOf.hlab_ofPlaceOK h i
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (codeOf (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r → (0 : Int64) = (RuntimeLayout.ofPlaceOK h i).lab r :=
    fun _ h => nomatch h
  exact {
    hd := blkPh_of_factOk hl hr hn (hf _ (by simp [mainPhTabS]))
    ld := step_of_factOk hl (hf (.step sc.sc 2) (by simp [mainPhTabS]))
    br := blkPh_of_factOk hl hr hn (hf _ (by simp [mainPhTabS]))
    fr := blkPh_of_factOk hl hr hn (hf _ (by simp [mainPhTabS]))
    call0 := blkPh_of_factOk hl hr hn (hf _ (by simp [mainPhTabS]))
    sp0 := blkPh_of_factOk hl hr hn (hf _ (by simp [mainPhTabS]))
    ex := blkPh_of_factOk hl hr hn (hf _ (by simp [mainPhTabS]))
    svc := step_of_factOk hl (hf (.step sc.sp1 3) (by simp [mainPhTabS])) }

/-- **`scc_rt_main`'s code and phase facts after a setup block** at an
output passing `placeOK` whose tail has one (A11): some `sw < 8` with the
runtime's code at `setupMC sw` and `MainPhS` there. -/
theorem mainPhS_of_placeOKAt (hs : o.place.tail = .setup) :
    ∃ sw < 8, rtCodeOkS o.prog (setupMC sw) = true ∧
      MainPhS (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
        (RuntimeLayout.ofPlaceOK h i).lab (setupMC sw) := by
  obtain ⟨sw, hsw, hc, hp⟩ := setupIn_of_placeOKAt h hs
  exact ⟨sw, hsw, hc, mainPhS_of_tab h i hp⟩

end Tab

/-! ## Under an unsatisfiable frame condition -/

section False

variable {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- `scc_rt_main`'s own obligations after a setup block under an
unsatisfiable frame condition. -/
theorem mainSW_ofFalse {ms : MemSide isaLSE2} {sc : SetupCode} {PostS : Ctl → Reg64s → Prop}
    {Post : Ctl → BitVec 64 → Prop} {g : MainG} {x0 : BitVec 64} (h : ∀ m, ¬ F m) :
    MainSW W K exe endPc R F ms sc PostS Post g x0 :=
  ⟨⟨blkW_ofFalse h, nodeW_ofFalse h, blkW_ofFalse h, blkW_ofFalse h⟩, blkW_ofFalse h, blkW_ofFalse h,
    ⟨blkW_ofFalse h, nodeW_ofFalse h⟩⟩

end False

/-! ## Inside `SFacts` -/

section Main

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

/-- No `ret` in a block: `hret` of `blkW_postO`, for any return address. -/
private theorem hnr {blk : List Directive} (hb : noRetBlk blk = true) {n : ND} {ra' : Int64} :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra' :=
  fun _ _ _ k hk r hr => (noRet_false hb k hk r hr).elim

set_option maxHeartbeats 800000 in
/-- **`scc_rt_main`'s own states after a setup block are inside `SFacts`**
(`MainSW`), for any program with its code (`hin`), in any 16-aligned region
holding its frame of `Z` with 8-aligned bounds, with the source control's
facts at the entry (`hC0`), back from the setup block under `PostS`
(`hPostS`) and at the return point under `Post` (`hPost`), its phase facts
(`hph`), the setup words and the TCB in the frame (`hsw`, `hZw`), the limit
word `limA g.tp` mapped (`hmr`) and unmapped in private memory under the
frame condition (`hun`), `rS` in the pool (`hsub`) and not wrapping
(`hfit`), and the frame condition giving the words of `rS` off the region
(`hFO`). -/
theorem mainSW_sfacts {ms : MemSide isaLSE2} {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {sc : SetupCode} (hin : mainSIn prog sc = true) {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    {g : MainG} {x0 : BitVec 64} (hC0 : CFacts Λ lbl g.c0) (hPostS : ∀ c rs, PostS c rs → CFacts Λ lbl c)
    (hPost : ∀ c v, Post c v → CFacts Λ lbl c) (hph : MainPhS okPc ph lab sc)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -sc.Z.toInt) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) (hsw : sc.sw ≤ 7) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    MainSW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F ms sc PostS Post g x0 := by
  have h := hin
  simp only [mainSIn, prologueIn, exitIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, -⟩, bCall⟩, -⟩, bMsh⟩, -⟩, bEx, bSvc⟩ := h
  have esc := label_labelGap hI.lays hgap
  rw [hI.labOk] at esc
  have hR8 : R.base.toNat % 8 = 0 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hI.labOk]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact blkW_postO hI bHd (by rw [esc, ofNat4_zero, ofNat4_zero]) (chkHead_ok _ _ _) hR hal hlo hhi
        (fun _ _ hJ => hJ.1.1 ▸ hC0) hph.hd (hnr (chkHead_noRet _)) (fun _ _ _ => rfl) hl hh hsub hfit hFO
    · exact nodeW_ldr_postO hI bLd rfl (by show _ + 4 + 4 = _; rw [esc, ofNat4_zero, pc2])
        (fun _ _ ⟨_, hJ, _⟩ => hJ.1.1 ▸ hC0) hph.ld.1 hph.ld.2
        (fun _ _ ⟨_, hJ, he⟩ => by rw [he, rAddr_chkRegs]; exact tcbA_limA hJ.1.2.2) hmr hun hR hR8 hl hh hsub
        hFO
    · exact blkW_postO hI bBr (by rw [esc, ofNat4_zero, pc3]; rfl) (chkBr_ok _ _ _ _) hR hal hlo hhi
        (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1.1 ▸ hC0) hph.br (hnr (chkBr_noRet _)) (fun _ _ _ => rfl) hl hh hsub hfit
        hFO
    · exact blkW_postO hI bFr (by rw [esc, ofNat4_zero, pc5]; rfl)
        (frameSet_ok (lo := -sc.Z.toInt) (hi := 0) h16 hZ (by omega) (Int.le_refl _)
          (by simp [Spike.Lib.offOk]; omega)) hR hal hlo hhi
        (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1.1 ▸ hC0) hph.fr (hnr (frameSet_noRet _)) (fun _ _ _ => rfl) hl hh hsub hfit
        hFO
  · rw [hI.labOk]
    exact blkW_postO hI bCall (ofNat4_zero _) (okBlk_blD _ _ _ _) hR hal hlo hhi (fun _ _ hJ => hJ.1 ▸ hC0)
      hph.call0 (hnr (blD_noRet _)) (fun _ _ _ => rfl) hl hh hsub hfit hFO
  · rw [hI.labOk]
    exact blkW_postO hI bMsh (ofNat4_zero _)
      (okBlk_marshal (lo := -sc.Z.toInt) (hi := 0) (by omega) hsw _
        (fun i hi => by simp [Spike.Lib.offOk]; omega) (by simp [Spike.Lib.offOk]; omega))
      hR hal hlo hhi (fun _ _ hJ => hPostS _ _ hJ.1) hph.sp0 (hnr (marshal_noRet _ _)) (fun _ _ _ => rfl) hl hh
      hsub hfit hFO
  · rw [hI.labOk]
    refine ⟨?_, ?_⟩
    · exact blkW_postO hI bEx (ofNat4_zero _) (exitTail_ok (lo := -sc.Z.toInt) (hi := 0) hk
          (by show (-sc.Z.toInt) % 16 = 0; omega)) hR hal hlo hhi (fun _ _ hJ => hPost _ _ hJ)
        hph.ex (hnr (exitTail_noRet _)) (fun _ _ _ => rfl) hl hh hsub hfit hFO
    · exact nodeW_svc_postO hI bSvc rfl (pc3 _).symm (fun _ _ ⟨_, _, hP, _⟩ => hPost _ _ hP) hph.svc.1
        hph.svc.2 hR hR8 hl hh hsub hFO (fun _ _ h => by rw [h.1]; decide)

end Main

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Rt.mainPhS_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainPhS_of_placeOKAt

/-- info: 'Spike.Lib.A64.Rt.mainSW_sfacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainSW_sfacts

end Spike.Lib.A64.Rt
